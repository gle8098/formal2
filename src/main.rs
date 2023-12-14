use std::fmt::{Debug, Display, Formatter};
use std::io;

use crate::earley::make_earley_parser;
use crate::lr1::make_lr1_parser;

mod earley;
mod lr1;

/// Пустое слово
const EPSILON: char = 'ε';
/// Начальный нетерминал, также известный как `S'`
const ALGO_START: char = '^';
/// Нетерминал конца слова
const ALGO_END: char = '$';

/// A → α
#[derive(Clone, Eq, Hash, PartialEq)]
#[allow(non_snake_case)]
pub struct Rule {
    A: char,
    alpha: String,
}

impl Debug for Rule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}→{}", self.A, self.alpha)
    }
}

impl Display for Rule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self, f)
    }
}

pub trait Parser {
    fn contains(&self, word: &str) -> bool;
}

type ParserBuilder = fn(grammar: Vec<Rule>) -> Result<Box<dyn Parser>, String>;

fn parse_grammar<'a, I>(rules: I) -> Vec<Rule> where
    I: Iterator<Item=&'a str>,
{
    let mut parsed_rules = vec![];
    for rule in rules {
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

fn main() -> io::Result<()> {
    let mut buffer = String::new();
    println!("Select parser: earley or lr1");

    io::stdin().read_line(&mut buffer)?;
    let parser_builder: ParserBuilder = match buffer.trim() {
        "earley" => make_earley_parser,
        "lr1" => make_lr1_parser,
        &_ => panic!("Unknown parser {}", buffer)
    };

    let mut grammar = vec![];
    println!("Write grammar rules line by line. To end loop, write '!'");
    loop {
        buffer.clear();
        io::stdin().read_line(&mut buffer)?;
        let rule = buffer.trim();
        if rule == "!" {
            break;
        } else {
            grammar.push(rule.to_string());
        }
    }
    let grammar = parse_grammar(grammar.iter().map(|x| x.as_str()));

    let parser = parser_builder(grammar);
    if let Err(err_text) = parser {
        println!("Cannot compile grammar. {}", err_text);
        return Ok(());
    }

    let parser = parser.unwrap();
    println!("Now enter words to check...");
    loop {
        buffer.clear();
        io::stdin().read_line(&mut buffer)?;
        let word = buffer.trim();
        if word == "!" {
            break;
        } else {
            let result = parser.contains(word);
            if result {
                println!("YES");
            } else {
                println!("NO");
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use debug_print::debug_println;

    use crate::{parse_grammar, ParserBuilder};
    use crate::earley::make_earley_parser;
    use crate::lr1::make_lr1_parser;

    fn test(parser_builder: ParserBuilder, parser_name: &str) {
        let algo_index = match parser_name {
            "earley" => 0,
            "lr1" => 1,
            _ => panic!("new parser added")
        };

        let cases = vec![
            (vec!["S->aSbS", "S->bSaS", "S->ε"], vec![true, false], vec![
                ("ababba", true)
            ]),
            (vec!["S->aSbS", "S->ε"], vec![true, true], vec![
                ("aababb", true),
                ("aabbba", false),
                ("aaababbb", true),
            ]),
            (vec!["S->Tca", "S->b", "T->Sa", "T->c", "S->aUac", "S->a", "U->aS", "U->c"], vec![true, false], vec![
                ("acacaca", true),
                ("ccbb", false),
            ]),
            (vec!["S->SaP", "S->P", "P->PbV", "P->V", "V->c", "V->d"], vec![true, true], vec![
                // NT: S, P, V; T: eof=$, +=a, *=b, int=c, id=d
                // Пример из Википедии
                ("aacbcbc", false),
                ("bc", false),
                ("cbdac", true),
                ("c", true),
            ]),
            (vec!["S->aSbS", "S->c"], vec![true, true], vec![
                ("aacbcbc", true),
                ("aacbcbacbc", true),
                ("abc", false),
            ]),
            (vec!["S->aT", "S->aSc", "T->Uc", "T->aT", "U->cVb", "U->aU", "V->cVb", "V->a"], vec![true, false], vec![
                // Пример из контрольной
                ("acabc", true),
                ("aaaaaccccabbbbcc", true),
                ("ccccabbbbcc", false),
            ]),
            (vec!["S->aSb", "S->SS", "S->ε"], vec![true, false], vec![
                ("aabb", true),
                ("abababaaababbabb", true),
                ("aaababbbb", false),
            ]),
            (vec!["S->A", "A->B", "B->C", "C->D", "D->a"], vec![true, true], vec![
                ("a", true),
                ("", false),
                ("b", false)
            ]),
            (vec!["S->BBB", "B->A", "A->ε"], vec![true, true], vec![
                ("", true),
                ("a", false)
            ]),
        ];

        for (i, case) in cases.iter().enumerate() {
            let grammar = parse_grammar(case.0.iter().map(|x| *x));
            let parse_grammar_res = case.1[algo_index];

            debug_println!("\n\n\n====== Case {} ======", i + 1);
            debug_println!("Grammar: {:?}\nIs in {} class: {}", grammar, parser_name, parse_grammar_res);

            match parser_builder(grammar) {
                Ok(parser) => {
                    assert_eq!(parse_grammar_res, true, "Grammar built without errors");

                    for (j, &(word, expected_result)) in case.2.iter().enumerate() {
                        debug_println!("\n------ Subcase {} ------", j + 1);
                        debug_println!("Word: {}\nExpected contains: {}", word, expected_result);
                        let result = parser.contains(word);
                        assert_eq!(result, expected_result);
                    }
                }
                Err(err_text) => {
                    assert_eq!(parse_grammar_res, false, "Builder error: {}", err_text);
                }
            };
        }
    }

    macro_rules! parser_tests {
    ($($name:ident: $value:expr)*) => {
        $(
            #[test]
            fn $name() {
                test($value, stringify!($name));
            }
        )*
        }
    }

    parser_tests! {
        earley: make_earley_parser
        lr1: make_lr1_parser
    }
}
