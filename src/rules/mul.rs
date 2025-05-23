use crate::trs::ConstantFold;
use crate::trs::Math;
use egg::rewrite as rw;
pub type Rewrite = egg::Rewrite<Math, ConstantFold>;
pub fn mul() -> Vec<Rewrite> {
    vec![
        //MUL RULES
        rw!("mul-comm"      ; "(* ?a ?b)"                   => "(* ?b ?a)"),
        rw!("mul-assoc"     ; "(* ?a (* ?b ?c))"            => "(* (* ?a ?b) ?c)"),
        rw!("mul-zero"      ; "(* ?a 0)"                    => "0"),
        rw!("mul-one"       ; "(* ?a 1)"                    => "?a"),
        rw!("mul-cancel-div"; "(* (/ ?a ?b) ?b)"            => "(- ?a (% ?a ?b))"),
        rw!("mul-max-min"   ; "(* (max ?a ?b) (min ?a ?b))" => "(* ?a ?b)"),
        rw!("div-cancel-mul"; "(/ (* ?y ?x) ?x)"            => "?y"),
    ]
}
