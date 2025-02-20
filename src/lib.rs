use std::{ffi::OsString, fs::File, io::Read, time::Instant};

use io::writer::write_results;
use std::time::Duration;

use structs::{ExpressionStruct, PaperResult, ResultStructure, Ruleset};
pub mod dataset;
pub mod io;
pub mod rules;
pub mod structs;
pub mod trs;

use trs::{
    prove, prove_expression_with_file_classes, prove_npp, prove_pulses, prove_pulses_npp, simplify,
};

/// Runs Simple Caviar to prove the expressions passed as vector using the different params passed. #[allow(dead_code)]
pub fn prove_expressions(
    exprs_vect: &[ExpressionStruct],
    ruleset: &Ruleset,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> Vec<ResultStructure> {
    println!("hey");

    //Initialize the results vector.
    let mut results = Vec::new();

    //For each expression try to prove it then push the results into the results vector.
    for expression in exprs_vect.iter() {
        println!("Starting Expression: {}", expression.index);
        let mut res = prove(
            expression.index,
            &expression.expression,
            ruleset,
            params,
            use_iteration_check,
            report,
        );
        res.add_halide(expression.halide_result.clone(), expression.halide_time);
        println!("result: {:?}", res.result);
        results.push(res);
    }
    results
}

/// Runs Caviar with Pulses on the expressions passed as vector using the different params passed.
#[allow(dead_code)]
pub fn prove_expressions_pulses(
    exprs_vect: &[ExpressionStruct],
    ruleset: &Ruleset,
    threshold: f64,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> Vec<ResultStructure> {
    //Initialize the results vector.
    let mut results = Vec::new();
    //For each expression try to prove it using Caviar with Pulses then push the results into the results vector.
    for expression in exprs_vect.iter() {
        println!("Starting Expression: {}", expression.index);
        let mut res = prove_pulses(
            expression.index,
            &expression.expression,
            ruleset,
            threshold,
            params,
            use_iteration_check,
            report,
        );
        res.add_halide(expression.halide_result.clone(), expression.halide_time);
        results.push(res);
    }
    results
}

/// Runs Caviar with NPP on the expressions passed as vector using the different params passed.
#[allow(dead_code)]
pub fn prove_expressions_npp(
    exprs_vect: &[ExpressionStruct],
    ruleset: &Ruleset,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> Vec<ResultStructure> {
    //Initialize the results vector.
    let mut results = Vec::new();

    //For each expression try to prove it using Caviar with NPP then push the results into the results vector.
    for expression in exprs_vect.iter() {
        println!("Starting Expression: {}", expression.index);
        let mut res = prove_npp(
            expression.index,
            &expression.expression,
            ruleset,
            params,
            use_iteration_check,
            report,
        );
        res.add_halide(expression.halide_result.clone(), expression.halide_time);
        results.push(res);
    }
    results
}

/// Runs  Caviar with Pulses and NPP on the expressions passed as vector using the different params passed.
#[allow(dead_code)]
pub fn prove_expressions_pulses_npp_paper(
    exprs_vect: &[(String, String)],
    ruleset: &Ruleset,
    threshold: f64,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> Vec<PaperResult> {
    //Initialize the results vector.
    let mut results = Vec::new();
    // For each expression try to prove it using Caviar with Pulses and NPP then push the results into the results vector.
    for expression in exprs_vect.iter() {
        println!("Starting Expression: {}", expression.0);
        let res = prove_pulses_npp(
            -1,
            &expression.1,
            ruleset,
            threshold,
            params,
            use_iteration_check,
            report,
        );
        // res.add_halide(expression.halide_result, expression.halide_time);
        results.push(PaperResult::new(
            expression.0.clone(),
            expression.1.clone(),
            if res.result { 1 } else { 0 },
        ));
    }
    results
}

///Runs Caviar with Pulses and NPP on the expressions passed as vector using the different params passed.
#[allow(dead_code)]
pub fn prove_expressions_pulses_npp(
    exprs_vect: &[ExpressionStruct],
    ruleset: &Ruleset,
    threshold: f64,
    params: (usize, usize, f64),
    use_iteration_check: bool,
    report: bool,
) -> Vec<ResultStructure> {
    //Initialize the results vector.
    let mut results = Vec::new();

    // For each expression try to prove it using Caviar with Pulses and NPP then push the results into the results vector.
    for expression in exprs_vect.iter() {
        println!("Starting Expression: {}", expression.index);
        results.push(prove_pulses_npp(
            expression.index,
            &expression.expression,
            ruleset,
            threshold,
            params,
            use_iteration_check,
            report,
        ));
    }
    results
}

/// Runs Caviar using hierarchical clusters of rules to prove the expressions passed as vector using the different params passed.
pub fn prove_clusters(
    path: OsString,
    exprs_vect: &[ExpressionStruct],
    params: (usize, usize, f64),
    count: usize,
    use_iteration_check: bool,
    report: bool,
) {
    //Read the clusters from the files generated using Python.
    let mut file = File::open(path).unwrap();
    let mut s = String::new();
    file.read_to_string(&mut s).unwrap();
    let classes = json::parse(&s).unwrap();

    //Initialization
    let mut results_structs = Vec::new();
    let mut results_proving_class = Vec::new();
    let mut results_exec_time = Vec::new();
    let start_t = Instant::now();
    let mut average;
    let mut prove_result: (ResultStructure, i64, Duration);
    let mut i;

    //For each expression try to prove it using the clusters generated one after the other.
    for expression in exprs_vect.iter() {
        if report {
            println!("Starting Expression: {}", expression.index);
        }
        i = 0;
        average = 0.0;
        loop {
            prove_result = prove_expression_with_file_classes(
                &classes,
                params,
                expression.index,
                &expression.expression.clone(),
                use_iteration_check,
                report,
            )
            .unwrap();
            if report {
                println!("Iter: {} | time: {}", i, prove_result.0.total_time);
            }
            average += prove_result.0.total_time;
            i += 1;
            if i == count || !prove_result.0.result {
                break;
            }
        }
        prove_result.0.total_time = average / (i as f64);
        results_structs.push(prove_result.0);
        results_proving_class.push(prove_result.1);
        results_exec_time.push(prove_result.2);
        if report {
            println!("Average time: {}", average / (i as f64));
        }
    }
    let duration = start_t.elapsed().as_secs();
    let exec_time: f64 = results_exec_time.iter().map(|i| i.as_secs() as f64).sum();
    if report {
        println!("Execution time : |{}| |{}|", duration, exec_time);
    }

    //Write the results into the results csv file.
    write_results(
        &format!(
            "results/k_{}_class_analysis_results_params_{}_{}_{}_exec_{}.csv",
            classes[0].len(),
            params.0,
            params.1,
            params.2,
            duration
        ),
        &results_structs,
    )
    .unwrap();
}

/// Runs Simple Caviar to simplify the expressions passed as vector using the different params passed.
#[allow(dead_code)]
pub fn simplify_expressions(
    exprs_vect: &[ExpressionStruct],
    ruleset: &Ruleset,
    params: (usize, usize, f64),
    report: bool,
) -> Vec<ResultStructure> {
    //Initialize the results vector.
    let mut results = Vec::new();

    //For each expression try to prove it then push the results into the results vector.
    for expression in exprs_vect.iter() {
        println!("Starting Expression: {}", expression.index);
        let mut res = simplify(
            expression.index,
            &expression.expression,
            ruleset,
            params,
            report,
        );
        res.add_halide(expression.halide_result.clone(), expression.halide_time);
        results.push(res);
    }
    results
}
