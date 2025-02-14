use std::error::Error;
use std::ffi::OsString;
use std::fs::File;
use std::io::Read;
use std::{env, usize};

use egg::{Applier, Pattern, Rewrite};

use crate::structs::ExpressionStruct;
use crate::structs::Rule;
use crate::trs::{ConstantFold, Math};

/// Reads expressions from a csv file into an ExpressionStruct Vector.
#[allow(dead_code)]
pub fn read_expressions(file_path: &OsString) -> Result<Vec<ExpressionStruct>, Box<dyn Error>> {
    // Declare the vector and the reader
    let mut expressions_vect = Vec::new();
    let file = File::open(file_path)?;
    let mut rdr = csv::Reader::from_reader(file);
    // Read each record and extract then cast the values.
    for result in rdr.records() {
        // get the String of the value
        let record = result?;
        let index: i32 = record[0].parse::<i32>().unwrap();
        let expression = &record[1];
        // Check if Halide's resluts are included then add them if they are
        let halide_result = &record[2];
        let halide_time = record[3].parse::<f64>().unwrap();
        // Push the new ExpressionStruct initialized with the values extracted into the vector.
        expressions_vect.push(ExpressionStruct::new(
            index,
            expression.to_string(),
            halide_result.to_string(),
            halide_time,
        ))
    }
    return Ok(expressions_vect);
}

///Reads the expressions in the format specified for the work done for the paper variant.
#[allow(dead_code)]
pub fn read_expressions_paper(
    file_path: &OsString,
) -> Result<Vec<(String, String)>, Box<dyn Error>> {
    let mut expressions_vect = Vec::new();
    let file = File::open(file_path)?;
    let mut rdr = csv::ReaderBuilder::new().delimiter(b';').from_reader(file);
    for result in rdr.records() {
        let record = result?;
        let infix = record[0].to_string();
        let prefix = record[1].to_string();
        expressions_vect.push((infix, prefix))
    }
    return Ok(expressions_vect);
}

/// Reads the rules from a CSV file then pareses them into a Rule Vector.
#[allow(dead_code)]
pub fn read_rules(file_path: &OsString) -> Result<Vec<Rule>, Box<dyn Error>> {
    let mut rules_vect: Vec<Rule> = Vec::new();
    let file = File::open(file_path)?;
    let mut rdr = csv::Reader::from_reader(file);
    for result in rdr.records() {
        let record = result?;
        let index: i32 = record[0].parse::<i32>().unwrap();
        let lhs = (&record[2]).to_string();
        let rhs = (&record[3]).to_string();
        let condition = (&record[4]).to_string();
        rules_vect.push(Rule::new(index, lhs, rhs, Some(condition)))
    }
    return Ok(rules_vect);
}

/// Reads the rules in the format that Ruler outputs.
pub fn read_chompy_rules(
    file_path: &OsString,
) -> Result<Vec<Rewrite<Math, ConstantFold>>, Box<dyn Error>> {
    // open the file
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
                Rewrite::new(name.clone(), l_pat.clone(), r_pat.clone()).unwrap()
            } else {
                Rewrite::new(name.clone(), l_pat.clone(), r_pat.clone()).unwrap()
            };

            if s.contains("<=>") {
                let backwards_name = make_name(&r_pat, &l_pat, cond.clone());

                let backwards = if let Some(cond) = cond {
                    Rewrite::new(backwards_name.clone(), r_pat.clone(), l_pat.clone()).unwrap()
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
    for (i, line) in rules.lines().enumerate() {
        if line.contains("if") {
            // just start with total rules.
            continue;
        }
        let (forwards, backwards) = from_string(line).unwrap();
        result.push(forwards);
        if let Some(backwards) = backwards {
            result.push(backwards);
        }
    }
    Ok(result)
}

///Gets the nth argument from the command line.
pub fn get_nth_arg(n: usize) -> Result<OsString, Box<dyn Error>> {
    match env::args_os().nth(n) {
        None => Err(From::from("expected 1 argument, but got none")),
        Some(file_path) => Ok(file_path),
    }
}

/// Gets the params passed to the runner from the command line
pub fn get_runner_params(start: usize) -> Result<(usize, usize, f64), Box<dyn Error>> {
    //Get the number of iterations from the command line else initialize it to a default value
    let iter = match env::args_os().nth(start) {
        None => 30,
        Some(i) => i.into_string().unwrap().parse::<usize>().unwrap(),
    };

    // Get the number of nodes from the command line else initialize it to a default value
    let nodes = match env::args_os().nth(start + 1) {
        None => 10000,
        Some(i) => i.into_string().unwrap().parse::<usize>().unwrap(),
    };

    //Get the timelimit from the command line else initialize it to a default value
    let time = match env::args_os().nth(start + 2) {
        None => 3.0,
        Some(i) => i.into_string().unwrap().parse::<f64>().unwrap(),
    };

    return Ok((iter, nodes, time));
}

///Reads the start and end expressions from the exprs file in the tmp folder (used for quick testing)
pub fn get_start_end() -> Result<(String, String), Box<dyn Error>> {
    let mut file = File::open("./tmp/exprs.txt")?;
    let mut s = String::new();
    file.read_to_string(&mut s)?;
    let v: Vec<&str> = s.split("\n").collect();
    return Ok((v[0].to_string(), v[1].to_string()));
}
