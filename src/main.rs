use std::env;

use caviar::io::reader::{get_nth_arg, get_runner_params, get_start_end, read_expressions};
use caviar::io::writer::write_results;

use caviar::dataset;
use caviar::structs::{Ruleset, RulesetTag};
use caviar::{
    prove_clusters, prove_expressions, prove_expressions_npp, prove_expressions_pulses,
    prove_expressions_pulses_npp, simplify_expressions,
};

use caviar::trs::simplify;

fn main() {
    let args: Vec<String> = env::args().collect();
    let ruleset: Ruleset = {
        if args.iter().last().unwrap() == "--use_chompy_rules" {
            println!("we're gonna use chompy rules.");
            Ruleset::new(RulesetTag::Custom("chompy-rules.txt".to_string()))
        } else if args.iter().last().unwrap() == "--only-total" {
            Ruleset::new(RulesetTag::CaviarOnlyTotal)
        } else {
            Ruleset::new(RulesetTag::CaviarAll)
        }
    };
    if args.len() > 4 {
        let operation = get_nth_arg(1).unwrap();
        let expressions_file = get_nth_arg(2).unwrap();
        let params = get_runner_params(3).unwrap();

        match operation.to_str().unwrap() {
            // Generates a dataset for minimum rulesets needed for each expression from the expressions file passed as argument
            "dataset" => {
                // cargo run --release dataset ./results/expressions_egg.csv 1000000 10000000 5 5 3 0 4
                let reorder_count = get_nth_arg(6)
                    .unwrap()
                    .into_string()
                    .unwrap()
                    .parse::<usize>()
                    .unwrap();
                let batch_size = get_nth_arg(7)
                    .unwrap()
                    .into_string()
                    .unwrap()
                    .parse::<usize>()
                    .unwrap();
                let continue_from_expr = get_nth_arg(8)
                    .unwrap()
                    .into_string()
                    .unwrap()
                    .parse::<usize>()
                    .unwrap();
                let cores = get_nth_arg(9)
                    .unwrap()
                    .into_string()
                    .unwrap()
                    .parse::<usize>()
                    .unwrap();
                rayon::ThreadPoolBuilder::new()
                    .num_threads(cores)
                    .build_global()
                    .unwrap();
                dataset::generation_execution(
                    &expressions_file,
                    params,
                    reorder_count,
                    batch_size,
                    continue_from_expr,
                );
            }

            // Prove expressions using Caviar with/without ILC
            "prove" => {
                let expression_vect = read_expressions(&expressions_file).unwrap();
                // use_iteration_check must be false on this branch
                let results = prove_expressions(&expression_vect, &ruleset, params, false, false);
                write_results("tmp/results_prove.csv", &results).unwrap();
            }
            // Prove expressions using Caviar with pulses and with/without ILC.
            "pulses" => {
                let threshold = get_nth_arg(6)
                    .unwrap()
                    .into_string()
                    .unwrap()
                    .parse::<f64>()
                    .unwrap();
                let expression_vect = read_expressions(&expressions_file).unwrap();
                let results = prove_expressions_pulses(
                    &expression_vect,
                    &ruleset,
                    threshold,
                    params,
                    true,
                    false,
                );
                write_results(&format!("tmp/results_beh_{}.csv", threshold), &results).unwrap();
            }
            // Prove expressions using Caviar with NPP and with/without ILC.
            "npp" => {
                let expression_vect = read_expressions(&expressions_file).unwrap();
                let results =
                    prove_expressions_npp(&expression_vect, &ruleset, params, true, false);
                write_results("tmp/results_fast.csv", &results).unwrap();
            }
            // Prove expressions using Caviar with Pulses and NPP and with pulses and with/without ILC.
            "pulses_npp" => {
                let threshold = get_nth_arg(6)
                    .unwrap()
                    .into_string()
                    .unwrap()
                    .parse::<f64>()
                    .unwrap();
                let expression_vect = read_expressions(&expressions_file).unwrap();
                let results = prove_expressions_pulses_npp(
                    &expression_vect,
                    &ruleset,
                    threshold,
                    params,
                    true,
                    false,
                );
                write_results(&format!("tmp/results_beh_npp_{}.csv", threshold), &results).unwrap();
            }
            // Prove expressions using Caviar with clusters of rules and with pulses and with/without ILC.
            "clusters" => {
                let expression_vect = read_expressions(&expressions_file).unwrap();
                let classes_file = get_nth_arg(6).unwrap();
                let iterations_count = get_nth_arg(7)
                    .unwrap()
                    .into_string()
                    .unwrap()
                    .parse::<usize>()
                    .unwrap();
                prove_clusters(
                    classes_file,
                    &expression_vect,
                    params,
                    iterations_count,
                    true,
                    true,
                );
            }
            "simplify" => {
                let expression_vect = read_expressions(&expressions_file).unwrap();
                let results = simplify_expressions(&expression_vect, &ruleset, params, true);
                write_results("tmp/results_simplify.csv", &results).unwrap();
            }
            _ => {}
        }
    } else {
        //Quick executions with default parameters
        let params = get_runner_params(1).unwrap();
        let (start, end) = get_start_end().unwrap();
        println!("Simplifying expression:\n {}\n to {}", start, end);
        //Example of NPP execution with default parameters
        println!("{:?}", simplify(-1, &start, &ruleset, params, true));
    }
}
