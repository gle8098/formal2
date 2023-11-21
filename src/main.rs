use std::fmt::{Debug, Formatter};

const EPSILON: char = 'ε';
const ALGO_START: char = '$';

/// A → α
#[derive(Clone, Eq, Hash, PartialEq)]
#[allow(non_snake_case)]
struct Rule {
    A: char,
    alpha: String,
}

impl Debug for Rule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}→{}", self.A, self.alpha)
    }
}

fn parse_grammar(rules: &[&str]) -> Vec<Rule> {
    let mut parsed_rules = Vec::with_capacity(rules.len());
    for rule in rules.iter() {
        let (mut left, mut right) = rule.split_once("->").expect("Rule does not have '->'");

        left = left.trim();
        assert_eq!(left.len(), 1, "Left side of a rule must have exactly one term");

        right = right.trim();
        if *right == EPSILON.to_string() {
            right = "";
        }

        parsed_rules.push(Rule { A: left.chars().nth(0).unwrap(), alpha: right.to_string() });
    }

    parsed_rules
}

fn main() {}