use crate::structs::{ResultStructure, Rule, Ruleset, RulesetTag};

use json::JsonValue;
use sexp::{parse, Sexp};
use std::error::Error;
use std::time::Duration;
use std::{cmp::Ordering, time::Instant};

use colored::*;
use egg::*;

// Defining aliases to reduce code.
pub type EGraph = egg::EGraph<Math, ConstantFold>;
pub type Rewrite = egg::Rewrite<Math, ConstantFold>;

//Definition of the language used.
define_language! {
    pub enum Math {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "%" = Mod([Id; 2]),
        "max" = Max([Id; 2]),
        "min" = Min([Id; 2]),
        "<" = Lt([Id; 2]),
        ">" = Gt([Id; 2]),
        "!" = Not(Id),
        "<=" = Let([Id;2]),
        ">=" = Get([Id;2]),
        "==" = Eq([Id; 2]),
        "!=" = IEq([Id; 2]),
        "||" = Or([Id; 2]),
        "&&" = And([Id; 2]),
        Constant(i64),
        Symbol(Symbol),
    }
}
/// Enabling Constant Folding through the Analysis of egg.
#[derive(Default, Clone)]
pub struct ConstantFold;

impl Analysis<Math> for ConstantFold {
    type Data = Option<i64>;

    fn merge(&self, a: &mut Self::Data, b: Self::Data) -> Option<Ordering> {
        match (a.as_mut(), &b) {
            (None, None) => Some(Ordering::Equal),
            (None, Some(_)) => {
                *a = b;
                Some(Ordering::Less)
            }
            (Some(_), None) => Some(Ordering::Greater),
            (Some(_), Some(_)) => Some(Ordering::Equal),
        }
        // if a.is_none() && b.is_some() {
        //     *a = b
        // }
        // cmp
    }

    fn make(egraph: &EGraph, enode: &Math) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref();
        Some(match enode {
            Math::Constant(c) => *c,
            Math::Add([a, b]) => x(a)? + x(b)?,
            Math::Sub([a, b]) => x(a)? - x(b)?,
            Math::Mul([a, b]) => x(a)? * x(b)?,
            // Math::Div([a, b]) if *x(b)? != 0 => (x(a)? / x(b)?),
            Math::Div([a, b]) => {
                if *x(b)? == 0 {
                    0
                } else {
                    x(a)? / x(b)?
                }
            }
            Math::Max([a, b]) => std::cmp::max(*x(a)?, *x(b)?),
            Math::Min([a, b]) => std::cmp::min(*x(a)?, *x(b)?),
            Math::Not(a) => {
                if *x(a)? == 0 {
                    1
                } else {
                    0
                }
            }
            Math::Lt([a, b]) => {
                if x(a)? < x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::Gt([a, b]) => {
                if x(a)? > x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::Let([a, b]) => {
                if x(a)? <= x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::Get([a, b]) => {
                if x(a)? >= x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::Mod([a, b]) => {
                if *x(b)? == 0 {
                    0
                } else {
                    x(a)? % x(b)?
                }
            }
            Math::Eq([a, b]) => {
                if x(a)? == x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::IEq([a, b]) => {
                if x(a)? != x(b)? {
                    1
                } else {
                    0
                }
            }
            Math::And([a, b]) => {
                if *x(a)? == 0 || *x(b)? == 0 {
                    0
                } else {
                    1
                }
            }
            Math::Or([a, b]) => {
                if *x(a)? == 1 || *x(b)? == 1 {
                    1
                } else {
                    0
                }
            }

            _ => return None,
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.data {
            let added = egraph.add(Math::Constant(c));
            let (id, _did_something) = egraph.union(id, added);
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

/// Checks if a constant is positive
pub fn is_const_pos(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    // Get the constant
    let var = var.parse().unwrap();

    // Get the substitutions where the constant appears
    move |egraph, _, subst| {
        // Check if any of the representations of ths constant (nodes inside its eclass) is positive
        egraph[subst[var]].nodes.iter().any(|n| match n {
            Math::Constant(c) => c > &0,
            _ => false,
        })
    }
}

/// Checks if a constant is negative
pub fn is_const_neg(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();

    // Get the substitutions where the constant appears
    move |egraph, _, subst| {
        //Check if any of the representations of ths constant (nodes inside its eclass) is negative
        egraph[subst[var]].nodes.iter().any(|n| match n {
            Math::Constant(c) => c < &0,
            _ => false,
        })
    }
}

/// Checks if a constant is equals zero
pub fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = Math::Constant(0);
    // Check if any of the representations of the constant (nodes inside its eclass) is zero
    move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
}

/// Generic condition handler. Takes in a program and returns if the e-graph
/// has figured out if it should hold. It is sound, but not complete.
/// (i.e., `is_true === true` means that the condition is definitely true,
/// but `is_true === false` does not mean that the condition is definitely false.)
pub fn is_true(prog: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let sexp: Sexp = parse(prog).unwrap();

    fn interpret_me(
        sexp: Sexp,
        egraph: &mut egg::EGraph<Math, ConstantFold>,
        id: Id,
        subst: &Subst,
    ) -> Option<i64> {
        match sexp {
            Sexp::Atom(a) => {
                // if it's a literal, return it
                if let Ok(num) = a.to_string().parse::<i64>() {
                    return Some(num);
                }
                // if it's a variable, return it
                let v: Var = a.to_string().parse().unwrap();
                if egraph[subst[v]].data.is_some() {
                    // See #12 -- is this different from what they do (they iterate through egraph[subst[v]].nodes and try to find a Constant)?
                    // if it is, why?
                    return Some(egraph[subst[v]].data.unwrap());
                } else {
                    return None;
                }
            }
            Sexp::List(ref l) => {
                // l[0] better be the operator.
                if let Sexp::Atom(a) = &l[0] {
                    let operand = a.to_string();

                    let children = l[1..]
                        .iter()
                        .map(|x| interpret_me(x.clone(), egraph, id, subst))
                        .collect::<Vec<_>>();

                    if children.iter().any(|x| x.is_none()) {
                        return None;
                    }

                    match children.len() {
                        1 => {
                            match operand.as_str() {
                                "!" => {
                                    // this is safe because of the check above which returns None if any of the children are None
                                    let val = children[0].unwrap();
                                    Some(if val == 0 { 1 } else { 0 })
                                },
                                "abs" => {
                                    let val = children[0].unwrap();
                                    Some(val.abs())
                                },
                                _ => panic!("Unary operator {} not supported", operand),
                            }
                        },
                        2 => {
                            match operand.as_str() {
                                "<" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(if val1 < val2 { 1 } else { 0 })
                                }
                                "<=" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(if val1 <= val2 { 1 } else { 0 })
                                }
                                ">" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(if val1 > val2 { 1 } else { 0 })
                                }
                                ">=" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(if val1 >= val2 { 1 } else { 0 })
                                }
                                "==" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(if val1 == val2 { 1 } else { 0 })
                                }
                                "!=" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(if val1 != val2 { 1 } else { 0 })
                                }
                                "-" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    val1.checked_sub(val2)
                                }
                                "&&" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(if val1 != 0 && val2 != 0 { 1 } else { 0 })
                                }
                                "||" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(if val1 != 0 || val2 != 0 { 1 } else { 0 })
                                }
                                "^" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    Some(val1 ^ val2)
                                }
                                "+" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    val1.checked_add(val2)
                                }
                                "*" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    val2.checked_mul(val2)
                                }
                                "/" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    if val2 == 0 {
                                        Some(0)
                                    } else {
                                        let is_neg = (val1 < 0) ^ (val2 < 0);
                                        if is_neg {
                                            val1.abs().checked_div(val2.abs()).map(|v| -v)
                                        } else {
                                            val1.checked_div(val2)
                                        }
                                    }
                                }
                                "%" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    if val2 == 0 {
                                        Some(0)
                                    } else {
                                        let is_neg = (val1 < 0) ^ (val2 < 0);
                                        if is_neg {
                                            val1.abs().checked_rem(val2.abs()).map(|v| -v)
                                        } else {
                                            val1.checked_rem(val2)
                                        }
                                    }
                                }
                                "min" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    if val1 < val2 {
                                        Some(val1)
                                    } else {
                                        Some(val2)
                                    }
                                }
                                "max" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    if val1 > val2 {
                                        Some(val1)
                                    } else {
                                        Some(val2)
                                    }
                                }
                                _ => panic!("Binary operator {} not supported", operand),
                            }
                        },
                        3 => {
                            match operand.as_str() {
                                "select" => {
                                    let val1 = children[0].unwrap();
                                    let val2 = children[1].unwrap();
                                    let val3 = children[2].unwrap();
                                    if val1 == 0 {
                                        Some(val2)
                                    } else {
                                        Some(val3)
                                    }
                                }
                                _ => panic!("Ternary operator {} not supported", operand),
                            }
                        }
                        _ => panic!("Sexp given: {}", sexp),
                    }
                } else {
                    panic!();
                }
            }
        }
    }

    move |egraph, id, subst| {
        let val = interpret_me(sexp.clone(), egraph, id, subst);
        val.is_some() && val.unwrap() != 0
    }
}

/// Eventually, we'll port this to the general `compare_c0_c1`, but we
/// need to handle things slightly differently given constants.
pub fn compare_c0_c1_chompy(
    e1: &str,
    e2: &str,
    comp: &str,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    // is there a more idiomatic way to do this in Rust?
    let e1_var: Option<Var> = match e1.parse() {
        Ok(v) => Some(v),
        Err(_) => None,
    };
    let e2_var: Option<Var> = match e2.parse() {
        Ok(v) => Some(v),
        Err(_) => None,
    };
    let i1: Option<i64> = match e1.parse() {
        Ok(c) => Some(c),
        Err(_) => None,
    };
    let i2: Option<i64> = match e2.parse() {
        Ok(c) => Some(c),
        Err(_) => None,
    };

    let f = match comp {
        "<" => i64::lt,
        "<=" => i64::le,
        "!=" => i64::ne,
        _ => panic!("Unsupported comparison: {}", comp),
    };

    move |egraph, _, subst| {
        // find the constant associated with e1.
        let c1: i64 = match (e1_var, i1) {
            // if it's a constant, just use that.
            (Some(_), Some(_)) => panic!("uhh"),
            (None, Some(c)) => c,
            (Some(v), None) => {
                let id = subst[v];
                match egraph[id].data {
                    Some(c) => c,
                    None => return false,
                }
            }
            _ => panic!("Why are both e1_var and i1 None?"),
        };
        let c2: i64 = match (e2_var, i2) {
            // if it's a constant, just use that.
            (Some(_), Some(_)) => panic!("uhh"),
            (None, Some(c)) => c,
            (Some(v), None) => {
                let id = subst[v];
                match egraph[id].data {
                    Some(c) => c,
                    None => return false,
                }
            }
            _ => panic!("Why are both e2_var and i2 None?"),
        };

        f(&c1, &c2)
    }
}

/// Compares two constants c0 and c1
pub fn compare_c0_c1(
    // first constant
    var: &str,
    // 2nd constant
    var1: &str,
    // the comparison we're checking
    comp: &'static str,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    // Get constants
    let var: Var = var.parse().unwrap();
    let var1: Var = var1.parse().unwrap();

    move |egraph, _, subst| {
        // Get the eclass of the first constant then match the values of its enodes to check if one of them proves the coming conditions
        egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
            // Get the eclass of the second constant then match it to c1
            Math::Constant(c1) => egraph[subst[var]].nodes.iter().any(|n| match n {
                // match the comparison then do it
                Math::Constant(c) => match comp {
                    "<" => c < c1,
                    "<a" => c < &c1.abs(),
                    "<=" => c <= c1,
                    "<=+1" => c <= &(c1 + 1),
                    "<=a" => c <= &c1.abs(),
                    "<=-a" => c <= &(-c1.abs()),
                    "<=-a+1" => c <= &(1 - c1.abs()),
                    ">" => c > c1,
                    ">a" => c > &c1.abs(),
                    ">=" => c >= c1,
                    ">=a" => c >= &(c1.abs()),
                    ">=a-1" => c >= &(c1.abs() - 1),
                    "!=" => c != c1,
                    "%0" => (*c1 != 0) && (c % c1 == 0),
                    "!%0" => (*c1 != 0) && (c % c1 != 0),
                    "%0<" => (*c1 > 0) && (c % c1 == 0),
                    "%0>" => (*c1 < 0) && (c % c1 == 0),
                    _ => false,
                },
                _ => false,
            }),
            _ => false,
        })
    }
}

/// Takes a JSON array of rules ids and return the vector of their associated Rewrites
pub fn filtered_rules(class: &json::JsonValue) -> Result<Vec<Rewrite>, Box<dyn Error>> {
    let ruleset = Ruleset::new(RulesetTag::CaviarAll);
    let all_rules = ruleset.rules();
    let rules_iter = all_rules.iter();
    let rules = rules_iter.filter(|rule| class.contains(rule.name()));
    let result: Vec<Rewrite> = rules.cloned().collect();
    Ok(result)
}

///Prints the egraph in an SVG file
#[allow(dead_code)]
pub fn print_graph(egraph: &EGraph, name: &str) {
    println!("printing graph to svg");
    egraph
        .dot()
        .to_svg("results/".to_owned() + name + ".svg")
        .unwrap();
    println!("done printing graph to svg");
}

#[allow(dead_code)]
/// Prints the most simplified version of the passed expression.
pub fn simplify(
    index: i32,
    start_expression: &str,
    ruleset: &Ruleset,
    params: (usize, usize, f64),
    report: bool,
) -> ResultStructure {
    let rules = ruleset.rules();
    //Parse the input expression
    let start: RecExpr<Math> = start_expression.parse().unwrap();

    //Initialize the runner and run it.
    let runner = Runner::default()
        .with_iter_limit(params.0)
        .with_node_limit(params.1)
        .with_time_limit(Duration::from_secs_f64(params.2))
        .with_expr(&start)
        .run(rules);

    //Get the ID of the root eclass.
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    //Initiate the extractor
    let mut extractor = Extractor::new(&runner.egraph, AstSize);

    //Extract the best expression
    let (_, best_expr) = extractor.find_best(id);
    println!(
        "Best Expr: {}",
        format!("{}", best_expr).bright_green().bold()
    );

    let total_time: f64 = runner.iterations.iter().map(|i| i.total_time).sum();
    if report {
        runner.print_report();
    }

    let stop_reason = match runner.stop_reason.unwrap() {
        StopReason::Saturated => "Saturation".to_string(),
        StopReason::IterationLimit(iter) => format!("Iterations: {}", iter),
        StopReason::NodeLimit(nodes) => format!("Node Limit: {}", nodes),
        StopReason::TimeLimit(time) => format!("Time Limit : {}", time),
        StopReason::Other(reason) => reason,
    };

    ResultStructure::new(
        index,
        start_expression.to_string(),
        best_expr.to_string(),
        true,
        best_expr.to_string(),
        ruleset.to_string(),
        runner.iterations.len(),
        runner.egraph.total_number_of_nodes(),
        runner.iterations.iter().map(|i| i.n_rebuilds).sum(),
        total_time,
        stop_reason,
        None,
    )
}

/// Checks if two expressions are equivalent
#[allow(dead_code)]
pub fn prove_equiv(
    start_expression: &str,
    end_expressions: &str,
    ruleset: &Ruleset,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> ResultStructure {
    let rules = ruleset.rules();
    let start: RecExpr<Math> = start_expression.parse().unwrap();
    let end: Pattern<Math> = end_expressions.parse().unwrap();
    let result: bool;
    let runner;
    let best_expr_string;
    // Initialize the runner and run it using the ILC contribution.
    if use_iteration_check {
        runner = Runner::default()
            .with_iter_limit(params.0)
            .with_node_limit(params.1)
            .with_time_limit(Duration::from_secs_f64(params.2))
            .with_expr(&start)
            .run_check_iteration(rules, &[end.clone()]);
    } else {
        // Initialize a simple runner and run it.
        runner = Runner::default()
            .with_iter_limit(params.0)
            .with_node_limit(params.1)
            .with_time_limit(Duration::from_secs_f64(params.2))
            .with_expr(&start)
            .run(rules);
    }
    // Get the ID of the root eclass.
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    // Check if the end expression matches any represenation of the root eclass.
    let matches = end.search_eclass(&runner.egraph, id);

    // if it doesn't match we extract the best expression of the first expression
    if matches.is_none() {
        let mut extractor = Extractor::new(&runner.egraph, AstDepth);
        let (_, best_expr) = extractor.find_best(id);
        best_expr_string = Some(best_expr.to_string());

        if report {
            println!(
                "{}\n{}\n",
                "Could not prove goal:".bright_red().bold(),
                end.pretty(40),
            );
            println!(
                "Best Expr: {}",
                format!("{}", best_expr).bright_green().bold()
            );
        }

        result = false;
    } else {
        if report {
            println!(
                "{}\n{}\n",
                "Proved goal:".bright_green().bold(),
                end.pretty(40)
            );
        }
        result = true;
        best_expr_string = Some(end.to_string())
    }
    //Total execution time of the runner
    let total_time: f64 = runner.iterations.iter().map(|i| i.total_time).sum();
    if report {
        runner.print_report();
    }

    let stop_reason = match runner.stop_reason.unwrap() {
        StopReason::Saturated => "Saturation".to_string(),
        StopReason::IterationLimit(iter) => format!("Iterations: {}", iter),
        StopReason::NodeLimit(nodes) => format!("Node Limit: {}", nodes),
        StopReason::TimeLimit(time) => format!("Time Limit : {}", time),
        StopReason::Other(reason) => reason,
    };

    ResultStructure::new(
        -1,
        start_expression.to_string(),
        end_expressions.to_string(),
        result,
        best_expr_string.unwrap_or_default(),
        ruleset.to_string(),
        runner.iterations.len(),
        runner.egraph.total_number_of_nodes(),
        runner.iterations.iter().map(|i| i.n_rebuilds).sum(),
        total_time,
        stop_reason,
        None,
    )
}

///Prove an expression to true or false using the given ruleset
#[allow(dead_code)]
pub fn prove(
    index: i32,
    start_expression: &str,
    ruleset: &Ruleset,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> ResultStructure {
    let rules = ruleset.rules();

    //Parse the input expression and the goals
    let start: RecExpr<Math> = start_expression.parse().unwrap();
    let end_1: Pattern<Math> = "1".parse().unwrap();
    let end_0: Pattern<Math> = "0".parse().unwrap();
    // Set up the goals we will check for.
    let goals = [end_0.clone(), end_1.clone()];
    let runner: Runner<Math, ConstantFold>;
    let mut result = false;
    let mut proved_goal_index = 0;

    let best_expr;

    if report {
        println!(
            "\n====================================\nProving Expression:\n {}\n",
            start_expression
        )
    }
    // Initialize the runner and run it using the ILC contribution.
    if use_iteration_check {
        runner = Runner::default()
            .with_iter_limit(params.0)
            .with_node_limit(params.1)
            .with_time_limit(Duration::from_secs_f64(params.2))
            .with_expr(&start)
            .run_check_iteration(rules, &goals);
    } else {
        // Initialize a simple runner and run it.
        runner = Runner::default()
            .with_iter_limit(params.0)
            .with_node_limit(params.1)
            .with_time_limit(Duration::from_secs_f64(params.2))
            .with_expr(&start)
            .run(rules);
    }
    // Get the ID of the root eclass.
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    // Check if the end expression matches any representation of the root eclass.
    for (goal_index, goal) in goals.iter().enumerate() {
        let boolean = (goal.search_eclass(&runner.egraph, id)).is_none();
        if !boolean {
            result = true;
            proved_goal_index = goal_index;
            break;
        }
    }

    if result {
        if report {
            println!(
                "{}\n{:?}",
                "Proved goal:".bright_green().bold(),
                goals[proved_goal_index].to_string()
            );
        }
        best_expr = Some(goals[proved_goal_index].to_string());
    } else {
        // If we couldn't prove the goal, we extract the best expression.
        let mut extractor = Extractor::new(&runner.egraph, AstDepth);
        let now = Instant::now();
        let (_, best_exprr) = extractor.find_best(id);
        let extraction_time = now.elapsed().as_secs_f32();

        best_expr = Some(best_exprr.to_string());

        if report {
            println!("{}\n", "Could not prove any goal:".bright_red().bold(),);
            println!(
                "Best Expr: {}",
                format!("{}", best_exprr).bright_green().bold()
            );
            println!(
                "{} {}",
                "Extracting Best Expression took:".bright_red(),
                extraction_time.to_string().bright_green()
            );
        }
    }
    let total_time: f64 = runner.iterations.iter().map(|i| i.total_time).sum();
    if report {
        runner.print_report();
    }

    let stop_reason = match runner.stop_reason.unwrap() {
        StopReason::Saturated => "Saturation".to_string(),
        StopReason::IterationLimit(iter) => format!("Iterations: {}", iter),
        StopReason::NodeLimit(nodes) => format!("Node Limit: {}", nodes),
        StopReason::TimeLimit(time) => format!("Time Limit : {}", time),
        StopReason::Other(reason) => reason,
    };

    ResultStructure::new(
        index,
        start_expression.to_string(),
        "1/0".to_string(),
        result,
        best_expr.unwrap_or_default(),
        ruleset.to_string(),
        runner.iterations.len(),
        runner.egraph.total_number_of_nodes(),
        runner.iterations.iter().map(|i| i.n_rebuilds).sum(),
        total_time,
        stop_reason,
        None,
    )
}

///Prove a rule by checking if the LHS of the rule matches the RHS using the cluster specified in the ruleset_class.
#[allow(dead_code)]
pub fn prove_rule(
    rule: &Rule,
    ruleset: &Ruleset,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> ResultStructure {
    //Check the equivalence of the LHS and RHS using the [`prove_equiv`] function.
    let mut result = prove_equiv(
        &rule.lhs,
        &rule.rhs,
        ruleset,
        params,
        use_iteration_check,
        report,
    );
    // Add the index of the rule and its condition to the result.
    result.add_index_condition(rule.index, rule.condition.as_ref().unwrap().clone());
    result
}

///Prove an expression to true or false using clusters of rules read from a file
pub fn prove_expression_with_file_classes(
    classes: &JsonValue,
    params: (usize, usize, f64),
    index: i32,
    start_expression: &str,
    use_iteration_check: bool,
    report: bool,
) -> Result<(ResultStructure, i64, Duration), Box<dyn Error>> {
    let start: RecExpr<Math> = start_expression.parse().unwrap();
    let mut result: bool = false;
    let mut runner: egg::Runner<Math, ConstantFold>;
    let mut rules: Vec<Rewrite>;
    let mut proved_goal_index = 0;

    let mut best_expr = Some("".to_string());
    let mut proving_class = -1;
    // First iteration of the runner.
    let end_1: Pattern<Math> = "1".parse().unwrap();
    let end_0: Pattern<Math> = "0".parse().unwrap();
    let goals = [end_0.clone(), end_1.clone()];
    let mut total_time: f64 = 0.0;

    let time_per_class = params.2 / (classes.len() as f64);

    // rules = filtered_rules(&classes[0])?;
    let start_t = Instant::now();
    runner = Runner::default()
        .with_iter_limit(params.0)
        .with_node_limit(params.1)
        .with_time_limit(Duration::from_secs_f64(time_per_class))
        .with_expr(&start);
    let id = runner.egraph.find(*runner.roots.last().unwrap());
    // End first iteration

    // Run the runner using the rulesets extracted from the file.
    for (i, class) in classes.members().enumerate() {
        rules = filtered_rules(class)?;
        if i > 0 {
            //Initialize the runner with the new ruleset.
            runner = Runner::default()
                .with_iter_limit(params.0)
                .with_node_limit(params.1)
                .with_time_limit(Duration::from_secs_f64(time_per_class))
                .with_egraph(runner.egraph)
        }

        if use_iteration_check {
            runner = runner.run_check_iteration_id(rules.iter(), &goals, id);
        } else {
            runner = runner.run(rules.iter());
        }
        // Get the execution time of the cluster of rules.
        let class_time: f64 = runner.iterations.iter().map(|i| i.total_time).sum();

        //Get the total execution of all executed clusters.
        total_time += class_time;

        //Check if the goal is contained in the root eclass of the egraph.
        for (goal_index, goal) in goals.iter().enumerate() {
            let boolean = (goal.search_eclass(&runner.egraph, id)).is_none();
            if !boolean {
                result = true;
                proved_goal_index = goal_index;
                break;
            }
        }

        if result {
            if report {
                println!(
                    "{}\n{:?}\n class {}",
                    "Proved goal:".bright_green().bold(),
                    goals[proved_goal_index].to_string(),
                    i
                );
            }
            best_expr = Some(goals[proved_goal_index].to_string())
        } else {
            let mut extractor = Extractor::new(&runner.egraph, AstDepth);
            // We want to extract the best expression represented in the
            // same e-class as our initial expression, not from the whole e-graph.
            // Luckily the runner stores the eclass Id where we put the initial expression.
            let (_, best_exprr) = extractor.find_best(id);
            best_expr = Some(best_exprr.to_string());

            if report {
                println!("{}\n", "Could not prove any goal:".bright_red().bold(),);
                println!(
                    "Best Expr: {}",
                    format!("{}", best_exprr).bright_green().bold()
                );
            }
        }
        if report {
            runner.print_report();
            println!(
                "Execution took: {}\n",
                format!("{} s", total_time).bright_green().bold()
            );
        }
        // If the expression is proved get the proving cluster and exit the loop.
        if result {
            proving_class = i as i64;
            break;
        }
    }

    let stop_reason = match runner.stop_reason.unwrap() {
        StopReason::Saturated => "Saturation".to_string(),
        StopReason::IterationLimit(iter) => format!("Iterations: {}", iter),
        StopReason::NodeLimit(nodes) => format!("Node Limit: {}", nodes),
        StopReason::TimeLimit(time) => format!("Time Limit : {}", time),
        StopReason::Other(reason) => reason,
    };
    let result_struct = ResultStructure::new(
        index,
        start_expression.to_string(),
        "1/0".to_string(),
        result,
        best_expr.unwrap_or_default(),
        format!("cluster {}", { proving_class }).to_string(),
        runner.iterations.len(),
        runner.egraph.total_number_of_nodes(),
        runner.iterations.iter().map(|i| i.n_rebuilds).sum(),
        total_time,
        stop_reason,
        None,
    );
    Ok((result_struct, proving_class, start_t.elapsed()))
}

///Checks if the variables passed match the confition specified for the impossible patterns.
pub fn impossible_conditions(
    condition: &str,
    variables: &Vec<&str>,
) -> impl Fn(&EGraph, &Subst) -> bool {
    let mut vars = Vec::new();
    for var in variables {
        let v: Var = var.parse().unwrap();
        vars.push(v)
    }
    let condition = condition.to_string();
    move |egraph, subst| match condition.as_str() {
        // v0 and v1: one var one const
        "c&v" => {
            let var = vars[0];
            let var1 = vars[1];
            egraph[subst[var]].nodes.iter().any(|n| match n {
                Math::Symbol(_) => egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                    Math::Constant(_) => true,
                    _ => false,
                }),
                Math::Constant(_) => egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                    Math::Symbol(_) => true,
                    _ => false,
                }),
                _ => false,
            })
        }
        // v0 and v1: one var one const
        // v2: const
        "c|v&v" => {
            let a = vars[0];
            let b = vars[1];
            let c = vars[2];
            egraph[subst[a]].nodes.iter().any(|n| match n {
                Math::Symbol(_) => egraph[subst[b]].nodes.iter().any(|n1| match n1 {
                    Math::Constant(vb) => {
                        (*vb != 0)
                            && egraph[subst[c]].nodes.iter().any(|n2| match n2 {
                                Math::Constant(_) => true,
                                _ => false,
                            })
                    }
                    _ => false,
                }),
                Math::Constant(va) => {
                    (*va != 0)
                        && egraph[subst[b]].nodes.iter().any(|n1| match n1 {
                            Math::Symbol(_) => egraph[subst[c]].nodes.iter().any(|n2| match n2 {
                                Math::Constant(_) => true,
                                _ => false,
                            }),
                            _ => false,
                        })
                }
                _ => false,
            })
        }
        // v0 and v1: one var one const
        // v2: const
        // if v1 const then v2 > - |v1| + 1
        "c<|b|" => {
            let x = vars[0];
            let b = vars[1];
            let c = vars[2];
            egraph[subst[x]].nodes.iter().any(|n| match n {
                Math::Symbol(_) => egraph[subst[b]].nodes.iter().any(|n1| match n1 {
                    Math::Constant(b_v) => egraph[subst[c]].nodes.iter().any(|n2| match n2 {
                        Math::Constant(c_v) => (*c_v > -b_v.abs()) && (*c_v < b_v.abs()),
                        _ => false,
                    }),
                    _ => false,
                }),
                _ => false,
            })
        }
        // v0 and v1: one var one const
        // v2: const
        // if v1 const then |v1| -1 > v2
        "c|v&v_|2|-1>3" => {
            let var0 = vars[0];
            let var1 = vars[1];
            let var2 = vars[2];
            egraph[subst[var0]].nodes.iter().any(|n| match n {
                Math::Symbol(_) => egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                    Math::Constant(b) => egraph[subst[var2]].nodes.iter().any(|n2| match n2 {
                        //c.abs() < (b.abs() - 1)
                        Math::Constant(c) => *c >= -(b.abs() - 1) && *c < b.abs(),
                        _ => false,
                    }),
                    _ => false,
                }),
                Math::Constant(_) => egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                    Math::Symbol(_) => egraph[subst[var2]].nodes.iter().any(|n2| match n2 {
                        Math::Constant(_) => true,
                        _ => false,
                    }),
                    _ => false,
                }),
                _ => false,
            })
        }
        // v0 , v1 , v2: 1 var 2 const
        // v3: const
        "c|c|v&c" => {
            let var0 = vars[0];
            let var1 = vars[1];
            let var2 = vars[2];
            let var3 = vars[3];
            egraph[subst[var3]].nodes.iter().any(|n3| match n3 {
                Math::Constant(_) => egraph[subst[var0]].nodes.iter().any(|n| match n {
                    Math::Symbol(_) => egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                        Math::Constant(_) => egraph[subst[var2]].nodes.iter().any(|n2| match n2 {
                            Math::Constant(_) => true,
                            _ => false,
                        }),
                        _ => false,
                    }),
                    Math::Constant(_) => egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                        Math::Symbol(_) => egraph[subst[var2]].nodes.iter().any(|n2| match n2 {
                            Math::Constant(_) => true,
                            _ => false,
                        }),
                        Math::Constant(_) => egraph[subst[var2]].nodes.iter().any(|n2| match n2 {
                            Math::Symbol(_) => true,
                            _ => false,
                        }),
                        _ => false,
                    }),
                    _ => false,
                }),
                _ => false,
            })
        }
        "cd-a%b=0" => {
            let a = vars[0];
            let x = vars[1];
            let b = vars[2];
            let c = vars[3];
            let d = vars[4];
            egraph[subst[a]].nodes.iter().any(|n1| match n1 {
                Math::Constant(va) => egraph[subst[b]].nodes.iter().any(|n2| match n2 {
                    Math::Constant(vb) => egraph[subst[c]].nodes.iter().any(|n3| match n3 {
                        Math::Constant(vc) => egraph[subst[d]].nodes.iter().any(|n4| match n4 {
                            Math::Constant(vd) => {
                                egraph[subst[x]].nodes.iter().any(|n5| match n5 {
                                    Math::Symbol(_) => (*vb != 0) && ((vc * vd - va) % vb == 0),
                                    _ => false,
                                })
                            }
                            _ => false,
                        }),
                        _ => false,
                    }),
                    _ => false,
                }),
                _ => false,
            })
        }
        // v0 , v1 , v2 , v3: 1 var 3 const
        // v4: const
        "c|c|c|v&c" => {
            let var0 = vars[0];
            let var1 = vars[1];
            let var2 = vars[2];
            let var3 = vars[3];
            let var4 = vars[4];
            egraph[subst[var4]].nodes.iter().any(|n4| match n4 {
                Math::Constant(_) => egraph[subst[var0]].nodes.iter().any(|n| match n {
                    Math::Symbol(_) => egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                        Math::Constant(_) => egraph[subst[var2]].nodes.iter().any(|n2| match n2 {
                            Math::Constant(_) => {
                                egraph[subst[var3]].nodes.iter().any(|n3| match n3 {
                                    Math::Constant(_) => true,
                                    _ => false,
                                })
                            }
                            _ => false,
                        }),
                        _ => false,
                    }),
                    Math::Constant(_) => egraph[subst[var1]].nodes.iter().any(|n1| match n1 {
                        Math::Symbol(_) => egraph[subst[var2]].nodes.iter().any(|n2| match n2 {
                            Math::Constant(_) => {
                                egraph[subst[var3]].nodes.iter().any(|n3| match n3 {
                                    Math::Constant(_) => true,
                                    _ => false,
                                })
                            }
                            _ => false,
                        }),
                        Math::Constant(_) => egraph[subst[var2]].nodes.iter().any(|n2| match n2 {
                            Math::Symbol(_) => {
                                egraph[subst[var3]].nodes.iter().any(|n3| match n3 {
                                    Math::Constant(_) => true,
                                    _ => false,
                                })
                            }
                            Math::Constant(_) => {
                                egraph[subst[var3]].nodes.iter().any(|n3| match n3 {
                                    Math::Symbol(_) => true,
                                    _ => false,
                                })
                            }
                            _ => false,
                        }),
                        _ => false,
                    }),
                    _ => false,
                }),
                _ => false,
            })
        }
        "v|c&c|c|v" => {
            let a = vars[0];
            let x = vars[1];
            let b = vars[2];
            let c = vars[3];
            let y = vars[4];
            egraph[subst[a]].nodes.iter().any(|n| match n {
                Math::Symbol(a_v) => egraph[subst[x]].nodes.iter().any(|n1| match n1 {
                    Math::Constant(x_v) => {
                        (*x_v != 0)
                            && egraph[subst[b]].nodes.iter().any(|n2| match n2 {
                                Math::Symbol(b_v) => {
                                    (a_v != b_v)
                                        && egraph[subst[c]].nodes.iter().any(|n3| match n3 {
                                            Math::Constant(c_v) => {
                                                (*c_v != 0)
                                                    && egraph[subst[y]].nodes.iter().any(|n4| {
                                                        match n4 {
                                                            Math::Constant(y_v) => *y_v != 0,
                                                            _ => false,
                                                        }
                                                    })
                                            }
                                            _ => false,
                                        })
                                }
                                Math::Constant(b_v) => {
                                    (*b_v != 0)
                                        && egraph[subst[c]].nodes.iter().any(|n3| match n3 {
                                            Math::Constant(c_v) => {
                                                (*c_v != 0)
                                                    && egraph[subst[y]].nodes.iter().any(|n4| {
                                                        match n4 {
                                                            Math::Symbol(y_v) => a_v != y_v,
                                                            _ => false,
                                                        }
                                                    })
                                            }
                                            _ => false,
                                        })
                                }

                                _ => false,
                            })
                    }
                    _ => false,
                }),
                Math::Constant(a_v) => {
                    (*a_v != 0)
                        && egraph[subst[x]].nodes.iter().any(|n1| match n1 {
                            Math::Symbol(x_v) => egraph[subst[b]].nodes.iter().any(|n2| match n2 {
                                Math::Symbol(b_v) => {
                                    (x_v != b_v)
                                        && egraph[subst[c]].nodes.iter().any(|n3| match n3 {
                                            Math::Constant(c_v) => {
                                                (*c_v != 0)
                                                    && egraph[subst[y]].nodes.iter().any(|n4| {
                                                        match n4 {
                                                            Math::Constant(y_v) => *y_v != 0,
                                                            _ => false,
                                                        }
                                                    })
                                            }
                                            _ => false,
                                        })
                                }
                                Math::Constant(b_v) => {
                                    (*b_v != 0)
                                        && egraph[subst[c]].nodes.iter().any(|n3| match n3 {
                                            Math::Constant(c_v) => {
                                                (*c_v != 0)
                                                    && egraph[subst[y]].nodes.iter().any(|n4| {
                                                        match n4 {
                                                            Math::Symbol(y_v) => y_v != x_v,
                                                            _ => false,
                                                        }
                                                    })
                                            }
                                            _ => false,
                                        })
                                }
                                _ => false,
                            }),
                            _ => false,
                        })
                }
                _ => false,
            })
        }
        "a<b" => {
            let a = vars[0];
            let b = vars[1];
            let x = vars[2];
            egraph[subst[a]].nodes.iter().any(|n| match n {
                Math::Constant(ca) => egraph[subst[b]].nodes.iter().any(|n1| match n1 {
                    Math::Constant(cb) => egraph[subst[x]].nodes.iter().any(|n2| match n2 {
                        Math::Symbol(_) => ca < cb,
                        _ => false,
                    }),
                    _ => false,
                }),
                _ => false,
            })
        }
        "b%a=0" => {
            let a = vars[0];
            let x = vars[1];
            let b = vars[2];
            egraph[subst[b]].nodes.iter().any(|n| match n {
                Math::Constant(vb) => egraph[subst[a]].nodes.iter().any(|n1| match n1 {
                    Math::Constant(va) => egraph[subst[x]].nodes.iter().any(|n2| match n2 {
                        Math::Symbol(_) => (*va != 0) && (vb % va == 0),
                        _ => false,
                    }),
                    Math::Symbol(_) => egraph[subst[x]].nodes.iter().any(|n2| match n2 {
                        Math::Constant(vx) => (*vx != 0) && (vb % vx == 0),
                        _ => false,
                    }),
                    _ => false,
                }),
                _ => false,
            })
        }
        _ => false,
    }
}

/// Macro that simplifies the definition of a non-provable pattern.
#[macro_export]
macro_rules! write_npp {
    // get the RHS and the condition
    (
        $rhs:tt;
        $cond:expr
    ) => {{
        // declare a math pattern for the RHS then return the pattern with the condition as a tuple
        let pattern: Pattern<Math> = $rhs.parse().unwrap();
        (pattern, $cond)
    }};
}

/// Prove an expression to true or false by using the Pulsing Caviar heuristic.
#[allow(dead_code)]
pub fn prove_pulses(
    index: i32,
    start_expression: &str,
    ruleset: &Ruleset,
    threshold: f64,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> ResultStructure {
    let rules = ruleset.rules();
    // Parse the start expression and the goals.
    let start: RecExpr<Math> = start_expression.parse().unwrap();
    let end_1: Pattern<Math> = "1".parse().unwrap();
    let end_0: Pattern<Math> = "0".parse().unwrap();

    // Put the goals we want to check in an array.
    let goals = [end_0.clone(), end_1.clone()];
    let mut result = false;
    let mut proved_goal_index = 0;
    let mut id;
    let best_expr;
    let mut total_time: f64 = 0.0;
    let nbr_passes = params.2 / threshold;

    if report {
        println!(
            "\n====================================\nProving Expression:\n {}\n",
            start_expression
        )
    }

    let mut i = 0.0;
    let mut exit = false;
    let mut expr = start;

    //Initialize the runner with the limits and the initial expression.
    let mut runner = Runner::default()
        .with_iter_limit(params.0)
        .with_node_limit(params.1)
        .with_time_limit(Duration::from_secs_f64(threshold))
        .with_expr(&expr);
    // Get the Id of the root eclass containing the initial expression.
    id = runner.egraph.find(*runner.roots.last().unwrap());
    // Run ES on each extracted expression until we reach a limit or we prove the expression.
    while !exit {
        if i > 0.0 {
            //Extract the best expression from the egraph.
            let mut extractor;
            extractor = Extractor::new(&(runner.egraph), AstDepth);

            //Calculate the extraction time.
            let now = Instant::now();
            let (_, best_exprr) = extractor.find_best(id);
            let extraction_time = now.elapsed().as_secs_f64();
            expr = best_exprr;
            total_time += extraction_time;
            if report {
                println!(
                    "Starting pass {} with Expr: {} in {}",
                    i,
                    format!("{}", expr).bright_green().bold(),
                    format!("{}", extraction_time).bright_green().bold()
                );
            }
        }
        //Rerun the ES on the newly extracted expression.
        if use_iteration_check {
            runner = Runner::default()
                .with_iter_limit(params.0)
                .with_node_limit(params.1)
                .with_time_limit(Duration::from_secs_f64(threshold))
                .with_expr(&expr)
                .run_check_iteration(rules, &goals);
        } else {
            runner = Runner::default()
                .with_iter_limit(params.0)
                .with_node_limit(params.1)
                .with_time_limit(Duration::from_secs_f64(threshold))
                .with_expr(&expr)
                .run(rules);
        }
        //Check if the expression is proved.
        id = runner.egraph.find(*runner.roots.last().unwrap());
        for (goal_index, goal) in goals.iter().enumerate() {
            let boolean = (goal.search_eclass(&runner.egraph, id)).is_none();
            if !boolean {
                result = true;
                proved_goal_index = goal_index;
                break;
            }
        }

        //If we saturate then the expression is unprovable using our ruleset.
        let saturated = match &runner.stop_reason.as_ref().unwrap() {
            StopReason::Saturated => true,
            _ => false,
        };
        let exec_time: f64 = runner.iterations.iter().map(|i| i.total_time).sum();
        total_time += exec_time;
        //Exit the loop if we saturated or reached the limits.
        if saturated || i > (nbr_passes - 1.0) || result {
            exit = true;
        } else {
            i += 1.0;
        }
    }
    if result {
        if report {
            println!(
                "{}\n{:?}",
                "Proved goal:".bright_green().bold(),
                goals[proved_goal_index].to_string()
            );
        }
        best_expr = Some(goals[proved_goal_index].to_string());
    } else {
        // If we didn't prove anything, then we return the best expression.
        let mut extractor = Extractor::new(&runner.egraph, AstDepth);
        let now = Instant::now();
        let (_, best_exprr) = extractor.find_best(id);
        let extraction_time = now.elapsed().as_secs_f32();

        best_expr = Some(best_exprr.to_string());
        if report {
            println!("{}\n", "Could not prove any goal:".bright_red().bold(),);
            println!(
                "Best Expr: {}",
                format!("{}", best_exprr).bright_green().bold()
            );
            println!(
                "{} {}",
                "Extracting Best Expression took:".bright_red(),
                extraction_time.to_string().bright_green()
            );
        }
    }
    if report {
        runner.print_report();
    }

    let stop_reason = match runner.stop_reason.unwrap() {
        StopReason::Saturated => "Saturation".to_string(),
        StopReason::IterationLimit(iter) => format!("Iterations: {}", iter),
        StopReason::NodeLimit(nodes) => format!("Node Limit: {}", nodes),
        StopReason::TimeLimit(time) => format!("Time Limit : {}", time),
        StopReason::Other(reason) => reason,
    };

    ResultStructure::new(
        index,
        start_expression.to_string(),
        "1/0".to_string(),
        result,
        best_expr.unwrap_or_default(),
        ruleset.to_string(),
        runner.iterations.len(),
        runner.egraph.total_number_of_nodes(),
        runner.iterations.iter().map(|i| i.n_rebuilds).sum(),
        total_time,
        stop_reason,
        None,
    )
}

/// Prove an expression to true or false by using the non-provable patterns technique.
#[allow(dead_code)]
pub fn check_npp(egraph: &EGraph, start_id: Id) -> (bool, String) {
    //Define the non-provable patterns.
    let impossibles = [
        // write_impo!("(== ?a ?x)";  impossible_conditions("c&v", &vec!["?a","?x"])),
        write_npp!("(!= ?a ?x)";  impossible_conditions("c&v", &vec!["?a","?x"])),
        // write_impo!("(< ?a ?x)" ;  impossible_conditions("c&v", &vec!["?a","?x"])),
        // write_impo!("(== (* ?a ?x) ?b)"; impossible_conditions("b%a=0", &vec!["?a","?x","?b"])),
        write_npp!("(!= (* ?a ?b) ?c)"; impossible_conditions("c|v&v", &vec!["?a","?b","?c"])),
        // write_impo!("(!= (/ ?a ?b) ?c)"; impossible_conditions("c|v&v", &vec!["?a","?b","?c"])),
        // // write_impo!("(<= (% ?a ?b) ?c)"; impossible_conditions("c|v&v_|2|-1>3", &vec!["?a","?b","?c"])),
        // // write_impo!("(<= ?c (% ?a ?b))"; impossible_conditions("c|v&v_3>-|2|+1", &vec!["?a","?b","?c"])),
        // write_impo!("(< ?c (% ?x ?b))"; impossible_conditions("c<|b|", &vec!["?x","?b","?c"])),
        // write_impo!("(< (% ?a ?b) ?c)"; impossible_conditions("c|v&v", &vec!["?a","?b","?c"])),
        // write_impo!("(== (/ (+ ?a ?x) ?b) ?c)"; impossible_conditions("c|c|v&c", &vec!["?a", "?x","?b","?c"])),
        write_npp!("(!= (/ (+ ?a ?x) ?b) ?c)"; impossible_conditions("c|c|v&c", &vec!["?a", "?x","?b","?c"])),
        // write_impo!("(== (/ (+ ?a (* ?x ?b)) ?c) ?d)"; impossible_conditions("cd-a%b=0", &vec!["?a", "?x","?b","?c","?d"])),
        write_npp!("(!= (/ (+ ?a (* ?x ?b)) ?c) ?d)"; impossible_conditions("c|c|c|v&c", &vec!["?a", "?x","?b","?c","?d"])),
        // write_impo!("(|| (< ?x ?a) (< ?b ?x))"; impossible_conditions("a<b", &vec!["?a","?b","?x"])),
        // write_impo!("(|| (< ?x ?a) (< ?b ?x))"; impossible_conditions("a<b", &vec!["?a","?b","?x"])),
        write_npp!("(!(&& (< ?a ?x) (< ?x ?b)))"; impossible_conditions("a<b", &vec!["?a","?b","?x"])),
        // write_impo!("(!(&& (< ?a ?x) (< ?x ?b)))"; impossible_conditions("a<b", &vec!["?a","?b","?x"])),
        // write_impo!("(== (* ?a ?x) (+ (* ?b ?y) ?c))"; impossible_conditions("v|c&c|c|v", &vec!["?a", "?x","?b","?c","?y"])),
    ];

    let mut proved_impo = false;
    let mut proved_impo_index = 0;
    // For each npp check if the empo matches the root eclass of the egraph
    for (impo_index, impo) in impossibles.iter().enumerate() {
        //check if the npp maches the root eclass of the egraph
        let results = match impo.0.search_eclass(egraph, start_id) {
            Option::Some(res) => res,
            _ => continue,
        };
        // Run the condition function then return the npp if the condition is true.
        if results.substs.iter().any(|subst| (impo.1)(egraph, subst)) {
            proved_impo = true;
            proved_impo_index = impo_index;
            break;
        }
    }
    (proved_impo, impossibles[proved_impo_index].0.to_string())
}

///Prove an expression using Pulses and the non-provable patterns.
#[allow(dead_code)]
pub fn prove_pulses_npp(
    index: i32,
    start_expression: &str,
    ruleset: &Ruleset,
    threshold: f64,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> ResultStructure {
    let rules = ruleset.rules();
    // Parse the start expression and the goals.
    let start: RecExpr<Math> = start_expression.parse().unwrap();
    let end_1: Pattern<Math> = "1".parse().unwrap();
    let end_0: Pattern<Math> = "0".parse().unwrap();
    let goals = [end_0.clone(), end_1.clone()];
    let mut result = false;
    let mut proved_goal_index = 0;
    let mut id;
    let best_expr;
    let mut total_time: f64 = 0.0;

    // Initialize the number of pulses based on the threshold passed as parameter.
    let nbr_passes = params.2 / threshold;

    if report {
        println!(
            "\n====================================\nProving Expression:\n {}\n",
            start_expression
        )
    }

    let mut i = 0.0;
    let mut exit = false;
    let mut expr = start;

    //Initialze the runner for the first Pulse
    let mut runner = Runner::default()
        .with_iter_limit(params.0)
        .with_node_limit(params.1)
        .with_time_limit(Duration::from_secs_f64(threshold))
        .with_expr(&expr);
    id = runner.egraph.find(*runner.roots.last().unwrap());
    while !exit {
        // Extract the best expression and reinitialize the runner if it's not the first pulse
        if i > 0.0 {
            //Extract the best expression and calculate the extraction time.
            let mut extractor;
            extractor = Extractor::new(&(runner.egraph), AstDepth);
            let now = Instant::now();
            let (_, best_exprr) = extractor.find_best(id);
            let extraction_time = now.elapsed().as_secs_f64();
            expr = best_exprr;
            total_time += extraction_time;

            if report {
                println!(
                    "Starting pass {} with Expr: {} in {}",
                    i,
                    format!("{}", expr).bright_green().bold(),
                    format!("{}", extraction_time).bright_green().bold()
                );
            }
        }

        if use_iteration_check {
            //Reinitialize the runner and run equality saturation using ILC
            let (temp_runner, impo_time) = Runner::default()
                .with_iter_limit(params.0)
                .with_node_limit(params.1)
                .with_time_limit(Duration::from_secs_f64(threshold))
                .with_expr(&expr)
                .run_fast(rules, &goals, check_npp);
            runner = temp_runner;
            total_time += impo_time;
        } else {
            //Reinitialize the runner and run equality saturation
            runner = Runner::default()
                .with_iter_limit(params.0)
                .with_node_limit(params.1)
                .with_time_limit(Duration::from_secs_f64(threshold))
                .with_expr(&expr)
                .run(rules);
        }

        //Check if one of the goals match the root eclass of the egraph.
        id = runner.egraph.find(*runner.roots.last().unwrap());
        for (goal_index, goal) in goals.iter().enumerate() {
            let boolean = (goal.search_eclass(&runner.egraph, id)).is_none();
            if !boolean {
                result = true;
                proved_goal_index = goal_index;
                break;
            }
        }

        //Check if the runner saturated or found an NPP
        let dont_continue = match &runner.stop_reason.as_ref().unwrap() {
            StopReason::Saturated => true,
            StopReason::Other(stop) => stop.contains("Impossible"),
            _ => false,
        };

        //Sum up the execution time
        let exec_time: f64 = runner.iterations.iter().map(|i| i.total_time).sum();
        total_time += exec_time;
        //Exit if the runner saturated, found an NPP or we reached the number of pulses or proved a result.
        if dont_continue || i > (nbr_passes - 1.0) || result {
            exit = true;
        } else {
            i += 1.0;
        }
    }
    if result {
        if report {
            println!(
                "{}\n{:?}",
                "Proved goal:".bright_green().bold(),
                goals[proved_goal_index].to_string()
            );
        }
        //Set the best expression to the goal matched.
        best_expr = Some(goals[proved_goal_index].to_string());
    } else {
        //Extract the best expression and calculate the extraction time if we can't prove.
        let mut extractor = Extractor::new(&runner.egraph, AstDepth);
        let now = Instant::now();
        let (_, best_exprr) = extractor.find_best(id);
        let extraction_time = now.elapsed().as_secs_f32();

        best_expr = Some(best_exprr.to_string());
        if report {
            println!("{}\n", "Could not prove any goal:".bright_red().bold(),);
            println!(
                "Best Expr: {}",
                format!("{}", best_exprr).bright_green().bold()
            );
            println!(
                "{} {}",
                "Extracting Best Expression took:".bright_red(),
                extraction_time.to_string().bright_green()
            );
        }
    }
    if report {
        runner.print_report();
    }

    let stop_reason = match runner.stop_reason.unwrap() {
        StopReason::Saturated => "Saturation".to_string(),
        StopReason::IterationLimit(iter) => format!("Iterations: {}", iter),
        StopReason::NodeLimit(nodes) => format!("Node Limit: {}", nodes),
        StopReason::TimeLimit(time) => format!("Time Limit : {}", time),
        StopReason::Other(reason) => reason,
    };

    ResultStructure::new(
        index,
        start_expression.to_string(),
        "1/0".to_string(),
        result,
        best_expr.unwrap_or_default(),
        ruleset.to_string(),
        runner.iterations.len(),
        runner.egraph.total_number_of_nodes(),
        runner.iterations.iter().map(|i| i.n_rebuilds).sum(),
        total_time,
        stop_reason,
        None,
    )
}

/// prove_npp runs caviar with the non-provable patterns
#[allow(dead_code)]
pub fn prove_npp(
    index: i32,
    start_expression: &str,
    ruleset: &Ruleset,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> ResultStructure {
    let rules = ruleset.rules();
    //Parse the start expression and goals then initialize the different used variables.
    let start: RecExpr<Math> = start_expression.parse().unwrap();
    let end_1: Pattern<Math> = "1".parse().unwrap();
    let end_0: Pattern<Math> = "0".parse().unwrap();
    let goals = [end_0.clone(), end_1.clone()];
    let runner: Runner<Math, ConstantFold>;
    let mut result = false;
    let mut proved_goal_index = 0;

    let best_expr;
    let mut total_time: f64 = 0.0;

    //print start expressions
    if report {
        println!(
            "\n====================================\nProving Expression:\n {}\n",
            start_expression
        )
    }
    // Enable the use of the iterative check technique
    if use_iteration_check {
        let (runner_temp, impo_time) = Runner::default()
            .with_iter_limit(params.0)
            .with_node_limit(params.1)
            .with_time_limit(Duration::from_secs_f64(params.2))
            .with_expr(&start)
            .run_fast(rules, &goals, check_npp);
        runner = runner_temp;
        total_time += impo_time;
    } else {
        //Run simple ES.
        runner = Runner::default()
            .with_iter_limit(params.0)
            .with_node_limit(params.1)
            .with_time_limit(Duration::from_secs_f64(params.2))
            .with_expr(&start)
            .run(rules);
    }
    //Get the id of the  eclass containing the input expression.
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    // Check if one of the goals matches
    for (goal_index, goal) in goals.iter().enumerate() {
        let boolean = (goal.search_eclass(&runner.egraph, id)).is_none();
        if !boolean {
            result = true;
            proved_goal_index = goal_index;
            break;
        }
    }

    if result {
        if report {
            println!(
                "{}\n{:?}",
                "Proved goal:".bright_green().bold(),
                goals[proved_goal_index].to_string()
            );
        }
        best_expr = Some(goals[proved_goal_index].to_string());
    } else {
        // If no goal was proved, then we need to extract the best expression
        let mut extractor = Extractor::new(&runner.egraph, AstDepth);
        let now = Instant::now();
        let (_, best_exprr) = extractor.find_best(id);

        // get the extraction time
        let extraction_time = now.elapsed().as_secs_f32();

        // get the best expression as string
        best_expr = Some(best_exprr.to_string());

        if report {
            println!("{}\n", "Could not prove any goal:".bright_red().bold(),);
            println!(
                "Best Expr: {}",
                format!("{}", best_exprr).bright_green().bold()
            );
            println!(
                "{} {}",
                "Extracting Best Expression took:".bright_red(),
                extraction_time.to_string().bright_green()
            );
        }
    }

    // Sum up the total execution time
    let total_time_runner: f64 = runner.iterations.iter().map(|i| i.total_time).sum();
    total_time += total_time_runner;
    if report {
        runner.print_report();
    }

    // Set the stop reason
    let stop_reason = match runner.stop_reason.unwrap() {
        StopReason::Saturated => "Saturation".to_string(),
        StopReason::IterationLimit(iter) => format!("Iterations: {}", iter),
        StopReason::NodeLimit(nodes) => format!("Node Limit: {}", nodes),
        StopReason::TimeLimit(time) => format!("Time Limit : {}", time),
        StopReason::Other(reason) => reason,
    };
    // Return a ResultStructure with all the information
    ResultStructure::new(
        index,
        start_expression.to_string(),
        "1/0".to_string(),
        result,
        best_expr.unwrap_or_default(),
        ruleset.to_string(),
        runner.iterations.len(),
        runner.egraph.total_number_of_nodes(),
        runner.iterations.iter().map(|i| i.n_rebuilds).sum(),
        total_time,
        stop_reason,
        None,
    )
}

#[allow(unused_imports)]
pub mod tests {
    use std::sync::Arc;

    use egg::{rewrite, EGraph};

    use super::{compare_c0_c1_chompy, ConstantFold, Math};

    #[test]
    pub fn test_chompy_comparators() {
        let rw =
            rewrite!("div_by_self"; "(/ ?x ?x)" => "1" if compare_c0_c1_chompy("?x", "0", "!="));
        let runner = egg::Runner::default()
            .with_expr(&"(/ x x)".parse().unwrap())
            .run(&[rw.clone()]);

        let mut extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);

        // right now, the condition should not be met.
        assert!(extractor.find_best(runner.roots[0]).1.to_string() != "1");

        // now, let's make the value of `x` 3.
        let mut egraph: EGraph<Math, ConstantFold> = EGraph::default();
        let x = egraph.add_expr(&"x".parse().unwrap());
        egraph[x].data = Some(3);

        let root = egraph.add_expr(&"(/ x x)".parse().unwrap());

        let runner = egg::Runner::default()
            .with_egraph(egraph.clone())
            .run(&[rw]);

        let mut extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);
        // now, the condition should be met.
        assert_eq!(extractor.find_best(root).1.to_string(), "1");
    }

    #[test]
    pub fn chompy_neq_equiv_to_caviar() {
        let mut egraph: EGraph<Math, ConstantFold> = EGraph::default();
        let x = egraph.add_expr(&"x".parse().unwrap());
        egraph[x].data = Some(3);

        let root = egraph.add_expr(&"(/ x x)".parse().unwrap());

        // 1. Chompy
        let runner = egg::Runner::default()
            .with_egraph(egraph.clone())
            .run(&[rewrite!(
                "div_by_self";
                "(/ ?x ?x)" => "1" if compare_c0_c1_chompy("?x", "0", "!=")
            )]);

        let mut extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);

        assert_eq!(extractor.find_best(root).1.to_string(), "1");

        // 2. Caviar
        let iter = crate::rules::div::div().into_iter();
        let div_cancel_rule = iter.filter(|r| r.name() == "div-cancel").next().unwrap();

        let runner = egg::Runner::default()
            .with_egraph(egraph.clone())
            .run(&[div_cancel_rule]);

        let mut extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);

        assert_eq!(extractor.find_best(root).1.to_string(), "1");
    }
}
