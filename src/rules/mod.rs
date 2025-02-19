use egg::Rewrite;

use crate::trs::{ConstantFold, Math};

pub mod add;
pub mod and;
pub mod andor;
pub mod div;
pub mod eq;
pub mod ineq;
pub mod lt;
pub mod max;
pub mod min;
pub mod modulo;
pub mod mul;
pub mod not;
pub mod or;
pub mod sub;

pub fn all_rules() -> Vec<Rewrite<Math, ConstantFold>> {
    vec![
        add::add(),
        and::and(),
        andor::andor(),
        div::div(),
        eq::eq(),
        ineq::ineq(),
        lt::lt(),
        max::max(),
        min::min(),
        modulo::modulo(),
        mul::mul(),
        not::not(),
        or::or(),
        sub::sub(),
    ]
    .into_iter()
    .flatten()
    .collect()
}

pub fn arith_rules() -> Vec<Rewrite<Math, ConstantFold>> {
    vec![
        add::add(),
        div::div(),
        modulo::modulo(),
        mul::mul(),
        sub::sub(),
    ]
    .into_iter()
    .flatten()
    .collect()
}

