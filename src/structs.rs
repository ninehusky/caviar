use std::{error::Error, ffi::OsString, usize};

use rand::seq::SliceRandom;

use egg::{Condition, ConditionalApplier, Pattern, Rewrite};
use serde::Serialize;
use sexp::{parse, Sexp};

use crate::trs::{compare_c0_c1_chompy, ConstantFold, Math};

#[derive(Serialize, Debug)]

/// The `structs` module contains a number of useful structs.
#[derive(Clone)]
pub enum RulesetTag {
    Custom(String),
    CaviarAll,
    CaviarOnlyArith,
}

/// A `Ruleset` is a collection of rules that can be used to prove or simplify an expression.
pub struct Ruleset {
    pub tag: RulesetTag,
    rules: Vec<Rewrite<Math, ConstantFold>>,
}

impl Ruleset {
    pub fn new(tag: RulesetTag) -> Self {
        let rules = Self::get_rules(&tag);
        Self { tag, rules }
    }

    pub fn rules(&self) -> &Vec<Rewrite<Math, ConstantFold>> {
        &self.rules
    }

    pub fn shuffle(&mut self, rng: &mut impl rand::Rng) {
        self.rules.shuffle(rng);
    }

    /// takes an class of rules to use then returns the vector of their associated Rewrites
    fn get_rules(ruleset_class: &RulesetTag) -> Vec<Rewrite<Math, ConstantFold>> {
        match ruleset_class {
            RulesetTag::Custom(path) => {
                let file_path = OsString::from(path);
                read_custom_rules(&file_path).unwrap()
            }
            RulesetTag::CaviarAll => crate::rules::all_rules(),
            RulesetTag::CaviarOnlyArith => crate::rules::arith_rules(),
        }
    }
}

impl ToString for Ruleset {
    fn to_string(&self) -> String {
        match &self.tag {
            RulesetTag::Custom(s) => s.to_string(),
            RulesetTag::CaviarAll => "CaviarAll".to_string(),
            RulesetTag::CaviarOnlyArith => "CaviarOnlyArith".to_string(),
        }
    }
}

impl From<i8> for Ruleset {
    fn from(value: i8) -> Self {
        // Observe that you can't construct a `ProvingRules::Custom` ruleset from this: this is purely
        // to work with the csvs that exist in the Caviar eval.
        match value {
            0 => Self::new(RulesetTag::CaviarOnlyArith),
            _ => Self::new(RulesetTag::CaviarAll),
        }
    }
}

/// Parses the file, which is in the format that Chompy outputs and returns the corresponding vector of Rewrite
/// rules. The conditions for the rules are limited to what can be expressed in
/// `compare_c0_c1_chompy`.
fn read_custom_rules(
    file_path: &OsString,
) -> Result<Vec<Rewrite<Math, ConstantFold>>, Box<dyn Error>> {
    println!("Reading rules from {}", file_path.to_str().unwrap());
    pub fn make_cond(cond: &str) -> impl Condition<Math, ConstantFold> {
        let cond_ast: Sexp = parse(cond).unwrap();
        let (cond, e1, e2) = match cond_ast {
            Sexp::Atom(_) => panic!("expected a list"),
            Sexp::List(l) => {
                if l.len() != 3 {
                    panic!("expected a list of length 3");
                }
                (
                    l[0].clone().to_string(),
                    l[1].clone().to_string(),
                    l[2].clone().to_string(),
                )
            }
        };

        compare_c0_c1_chompy(e1.as_str(), e2.as_str(), cond.as_str())
    }

    pub fn from_string(
        s: &str,
    ) -> Result<
        (
            Rewrite<Math, ConstantFold>,
            Option<Rewrite<Math, ConstantFold>>,
        ),
        String,
    > {
        let make_name =
            |lhs: &Pattern<Math>, rhs: &Pattern<Math>, cond: Option<Pattern<Math>>| -> String {
                match cond {
                    None => format!("{} ==> {}", lhs, rhs),
                    Some(cond) => format!("{} ==> {} if {}", lhs, rhs, cond),
                }
            };

        let (s, cond) = {
            if let Some((l, r)) = s.split_once(" if ") {
                let cond: Pattern<Math> = r.parse().unwrap();
                (l, Some(cond))
            } else {
                (s, None)
            }
        };
        if let Some((l, r)) = s.split_once("=>") {
            let l_pat: Pattern<Math> = l.parse().unwrap();
            let r_pat: Pattern<Math> = r.parse().unwrap();

            let name = make_name(&l_pat, &r_pat, cond.clone());

            let forwards = if let Some(ref cond) = cond {
                let conditional_applier = ConditionalApplier {
                    condition: make_cond(cond.to_string().as_str()),
                    applier: r_pat.clone(),
                };

                Rewrite::new(name.clone(), l_pat.clone(), conditional_applier).unwrap()
            } else {
                Rewrite::new(name.clone(), l_pat.clone(), r_pat.clone()).unwrap()
            };

            if s.contains("<=>") {
                let backwards_name = make_name(&r_pat, &l_pat, cond.clone());

                let backwards = if let Some(cond) = cond {
                    panic!(
                        "Why do we have a bidirectional rule with a condition? {:?}",
                        cond
                    );
                } else {
                    Rewrite::new(backwards_name.clone(), r_pat.clone(), l_pat.clone()).unwrap()
                };

                Ok((forwards, Some(backwards)))
            } else {
                Ok((forwards, None))
            }
        } else {
            Err(format!("Failed to parse {}", s))
        }
    }
    let rules = std::fs::read_to_string(file_path)?;
    let mut result = vec![];
    for line in rules.lines() {
        let (forwards, backwards) = from_string(line).unwrap();
        result.push(forwards);
        if let Some(backwards) = backwards {
            result.push(backwards);
        }
    }
    Ok(result)
}

//The `ExpressionStruct` type is used to represent an expression
#[derive(Serialize, Debug)]
pub struct ExpressionStruct {
    //index of the expression
    pub index: i32,
    // the string of the expression
    pub expression: String,
    // Halide's result for proving the expression
    pub halide_result: String,
    // The time it took halide to prove the expression
    pub halide_time: f64,
}

impl ExpressionStruct {
    //Constructor of ExpressionStruct
    pub fn new(index: i32, expression: String, halide_result: String, halide_time: f64) -> Self {
        Self {
            index,
            expression,
            halide_result,
            halide_time,
        }
    }
}

#[derive(Serialize, Debug)]
///The `ResultStructure` type is used to represent the result of proving or simplifying an expression
pub struct ResultStructure {
    //index of the expression set to make debugging easier
    pub index: i32,
    // The expression to be proved or simplified
    pub start_expression: String,
    // The goal to prove
    pub end_expression: String,
    // The result of the prover true means we could prove it.
    pub result: bool,
    // The simplest representation extracted
    pub best_expr: String,
    //The id of the cluster that was used to prove the expression in case we used clusters
    pub class: String,
    //Number of iterations used to prove the expression
    pub iterations: usize,
    //The size of the egraph used to prove the expression
    pub egraph_size: usize,
    //The number of rebuilds used to prove the expression
    pub rebuilds: usize,
    //The time it took to prove the expression
    pub total_time: f64,
    // The reason the execution stopped
    pub stop_reason: String,
    //The condition of the rule
    pub condition: Option<String>,
    // Halide's result for proving the expression
    pub halide_result: String,
    // The time it took halide to prove the expression
    pub halide_time: f64,
}

impl ResultStructure {
    //Constructor for the ResultStructure
    pub fn new(
        index: i32,
        start_expression: String,
        end_expression: String,
        result: bool,
        best_expr: String,
        class: String,
        iterations: usize,
        egraph_size: usize,
        rebuilds: usize,
        total_time: f64,
        stop_reason: String,
        condition: Option<String>,
        // halide_result: bool,
        // halide_time: f64
    ) -> Self {
        Self {
            index,
            start_expression,
            end_expression,
            result,
            best_expr,
            class,
            iterations,
            egraph_size,
            rebuilds,
            total_time,
            stop_reason,
            condition,
            halide_result: "false".to_string(),
            halide_time: 0.0,
        }
    }

    //adds index and the condition to the result
    pub fn add_index_condition(&mut self, index: i32, condition: String) {
        self.index = index;
        self.condition = Some(condition);
    }

    pub fn add_halide(&mut self, halide_result: String, halide_time: f64) {
        self.halide_result = halide_result;
        self.halide_time = halide_time;
    }
}

//The `Rule` type is used to represent a a Rule
#[derive(Serialize, Debug)]
pub struct Rule {
    //index of the rule
    pub index: i32,
    // the LHS of the rule
    pub lhs: String,
    // the RHS of the rule
    pub rhs: String,
    // The condition to apply the rule
    pub condition: Option<String>,
}

impl Rule {
    // Constructor of Rule
    #[allow(dead_code)]
    pub fn new(index: i32, lhs: String, rhs: String, condition: Option<String>) -> Self {
        Self {
            index,
            lhs,
            rhs,
            condition,
        }
    }
}

//a Structure used the result of  special expressions issued from halide for the implementation of the paper.
#[derive(Serialize, Debug)]
pub struct PaperResult {
    infix: String,
    prefix: String,
    result: i8,
}

impl PaperResult {
    pub fn new(infix: String, prefix: String, result: i8) -> Self {
        Self {
            infix,
            prefix,
            result,
        }
    }
}
