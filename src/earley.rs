use std::cell::{RefCell, RefMut};
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::sync::Arc;

use debug_print::debug_println;
use once_cell::sync::Lazy;

use crate::{ALGO_START, EPSILON, Rule};

static ENTRY_RULE: Lazy<Rule> = Lazy::new(|| Rule { A: ALGO_START, alpha: "S".to_string() });
static EMPTY_HASH_SET: Lazy<HashSet<Situation>> = Lazy::new(|| HashSet::new());


/// (A → α•β, i)
#[derive(Clone, Eq, Hash, PartialEq)]
struct Situation {
    rule: Arc<Rule>,

    // \in [0, |w|]
    dot_index: usize,

    // i in lecture's notation
    origin: usize,
}

impl Situation {
    /// Returns term right after dot (may be epsilon)
    pub fn dot_term(&self) -> char {
        self.rule.alpha.chars().nth(self.dot_index).unwrap_or(EPSILON)
    }
}

impl Debug for Situation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}→{}•{}, {})", self.rule.A, &self.rule.alpha[..self.dot_index], &self.rule.alpha[self.dot_index..],
               self.origin)
    }
}

/// Situation set at input position `j`
struct D {
    input_position: usize,

    /// all situations inside D_j with fast search by dot term
    situations: HashMap<char, HashSet<Situation>>,

    /// D struct keeps track of recently added situations, and stores some information about them. Call `take_deltas()`
    /// to get these deltas and reset them.

    /// Set of all terms after dot in recently added situations
    delta_dot_terms: HashSet<char>,
    /// All recently added situations, which have dot at the end of their rules
    delta_ended_sit: Vec<Situation>,

    stat_add_accepted: usize,
    stat_add_rejected: usize,
}

impl D {
    pub fn new(input_position: usize) -> Self {
        D {
            input_position,
            situations: HashMap::new(),
            delta_dot_terms: HashSet::new(),
            delta_ended_sit: Vec::new(),
            stat_add_accepted: 0,
            stat_add_rejected: 0,
        }
    }

    pub fn add_situation(&mut self, situation: Situation) -> bool {
        debug_println!("Add: {:?} ∈ D_{}", situation, self.input_position);

        let newly_inserted = self.situations.entry(situation.dot_term()).or_default()
            .insert(situation.clone());

        if newly_inserted {
            self.stat_add_accepted += 1;
            self.delta_dot_terms.insert(situation.dot_term());
            if situation.dot_term() == EPSILON {
                self.delta_ended_sit.push(situation);
            }
        } else {
            self.stat_add_rejected += 1;
        }

        newly_inserted
    }

    pub fn get_by_dot_term(&self, term: &char) -> &HashSet<Situation> {
        self.situations.get(term).unwrap_or(&EMPTY_HASH_SET)
    }

    pub fn take_deltas(&mut self) -> (HashSet<char>, Vec<Situation>) {
        (std::mem::take(&mut self.delta_dot_terms), std::mem::take(&mut self.delta_ended_sit))
    }
}

struct EarleyAlgorithm {
    grammar: Vec<Arc<Rule>>,
    /// lazy computed set of non-terminals that derive epsilon
    nullable_nonterminals: HashSet<char>,
    /// vector of situations set (index = input position in word)
    d_s: Vec<RefCell<D>>,
    word: String,
    word_ind: usize,
}

impl EarleyAlgorithm {
    pub fn new(grammar: Vec<Rule>) -> Self {
        let mut algo_grammar = vec![Arc::from(ENTRY_RULE.clone())];

        for rule in grammar {
            assert_ne!(rule.A, ALGO_START);
            algo_grammar.push(Arc::from(rule));
        }

        EarleyAlgorithm {
            grammar: algo_grammar,
            nullable_nonterminals: HashSet::new(),
            d_s: vec![],
            word: String::new(),
            word_ind: 0,
        }
    }

    fn entry_rule(&self) -> Arc<Rule> {
        self.grammar.first().unwrap().clone()
    }

    fn curr_d(&self) -> RefMut<D> {
        self.d_s.get(self.word_ind).unwrap().borrow_mut()
    }

    fn has_finish(&self) -> bool {
        self.d_s.last().unwrap().borrow().get_by_dot_term(&EPSILON)
            .contains(&Situation { rule: self.entry_rule(), dot_index: 1, origin: 0 })
    }

    fn update_nullable_nonterminals(&mut self, curr_delta_ended_sits: &Vec<Situation>) {
        for situation in curr_delta_ended_sits {
            // this is dot-ended situation
            debug_assert_eq!(situation.dot_term(), EPSILON);

            // ... and origin is the same with word index
            if situation.origin == self.word_ind {
                // => rule.A is nullable
                self.nullable_nonterminals.insert(situation.rule.A);
            }
        }
    }

    /// Produces new situations by rule: `(A→α•uβ, i, j) + /self.word[j] == u/ ---> (A→αu•β, i, j + 1)`.
    fn scan(&mut self) {
        let next_char = self.word.chars().nth(self.word_ind).unwrap();
        let prev_d = self.d_s.get(self.word_ind).unwrap().borrow();
        let mut curr_d = self.d_s.get(self.word_ind + 1).unwrap().borrow_mut();

        for situation in prev_d.get_by_dot_term(&next_char) {
            curr_d.add_situation(Situation {
                rule: situation.rule.clone(),
                dot_index: situation.dot_index + 1,
                origin: situation.origin,
            });
        }

        self.word_ind += 1;
    }

    /// Produces new situations by rule: `(A→α•Bβ, i, j) + /(B→γ) ∈ self.grammar/ ---> (B→•γ, j, j)`.
    fn predict(&mut self, curr_delta_dot_terms: &HashSet<char>) {
        let mut curr_d = self.curr_d();

        for rule in &self.grammar {
            if curr_delta_dot_terms.contains(&rule.A) {
                curr_d.add_situation(Situation {
                    rule: rule.clone(),
                    dot_index: 0,
                    origin: self.word_ind,
                });
            }
        }
    }

    /// Produces new situations by rule: `(A→α•Bβ, i, k) + (B→γ•, k, j) ---> (A→αB•β, i, j)`.
    fn complete(&mut self, curr_delta_ended_sits: &Vec<Situation>) {
        let curr_d = self.d_s.get(self.word_ind).unwrap().borrow();
        let mut new_situations = vec![];

        for situation in curr_delta_ended_sits {
            let origin_d = self.d_s.get(situation.origin).unwrap().borrow();
            for origin_sit in origin_d.get_by_dot_term(&situation.rule.A) {
                new_situations.push(Situation {
                    rule: origin_sit.rule.clone(),
                    origin: origin_sit.origin,
                    dot_index: origin_sit.dot_index + 1,
                });
            }
        }
        drop(curr_d);

        /// As can be seen from the arguments, we make `complete` dependent only on new rules of the form (B→γ•, k, j).
        /// However, it is possible that for the current `word_ind` a rule (A→α•Bβ, i, j) will be created for which the
        /// second argument of a form (B→γ•, j, j) has already been added. It's easy to see that in this case B must be
        /// nullable. To cover this case, we create new situations (A→αB•β, i, j).
        let mut i = 0;
        while i < new_situations.len() {
            let situation = &new_situations[i];
            if self.nullable_nonterminals.contains(&situation.dot_term()) {
                let mut situation = situation.clone();
                situation.dot_index += 1;
                new_situations.push(situation);
                // ... push the situation to the end of the vector to process it once again later
                // (maybe it has a few nullable non-terminals in a row)
            }
            i += 1;
        }

        let mut curr_d = self.curr_d();
        for situation in new_situations {
            curr_d.add_situation(situation);
        }
    }

    pub fn check_word(&mut self, word: String) -> bool {
        self.d_s = Vec::with_capacity(word.len() + 1);
        for j in 0..=word.len() {
            self.d_s.push(RefCell::new(D::new(j)));
        }

        self.word = word;
        self.word_ind = 0;

        self.d_s.get(0).unwrap().borrow_mut().add_situation(Situation {
            rule: self.entry_rule(),
            dot_index: 0,
            origin: 0,
        });

        loop {
            loop {
                let (curr_delta_dot_terms, curr_delta_ended_sits) = self.curr_d().take_deltas();
                if curr_delta_dot_terms.is_empty() && curr_delta_ended_sits.is_empty() {
                    break;
                }

                self.update_nullable_nonterminals(&curr_delta_ended_sits);
                self.complete(&curr_delta_ended_sits);
                self.predict(&curr_delta_dot_terms);
            }

            if self.word_ind == self.word.len() {
                break;
            }

            self.scan();
        }

        self.has_finish()
    }

    pub fn get_situations_stats(&self) -> (/*situations added*/ usize, /*times situation add rejected*/ usize) {
        let mut added = 0;
        let mut rejected = 0;
        for d in self.d_s.iter().map(|x| x.borrow()) {
            added += d.stat_add_accepted;
            rejected += d.stat_add_rejected;
        }
        (added, rejected)
    }
}

#[cfg(test)]
mod tests {
    use debug_print::debug_println;

    use crate::earley::EarleyAlgorithm;
    use crate::parse_grammar;

    #[test]
    fn test() {
        let cases = vec![
            (vec!["S->aSbS", "S->bSaS", "S->ε"], "ababba", true),
            (vec!["S->aSbS", "S->ε"], "aababb", true),
            (vec!["S->aSbS", "S->ε"], "aabbba", false),
            (vec!["S->aSbS", "S->ε"], "aaababbb", true),
            (vec!["S->Tca", "S->b", "T->Sa", "T->c", "S->aUac", "S->a", "U->aS", "U->c"], "acacaca", true),
            (vec!["S->Tca", "S->b", "T->Sa", "T->c", "S->aUac", "S->a", "U->aS", "U->c"], "ccbb", false),
            (vec!["S->A", "A->B", "B->C", "C->D", "D->a"], "a", true),
            (vec!["S->BBB", "B->A", "A->ε"], "", true),
        ];

        for (i, case) in cases.iter().enumerate() {
            let grammar = parse_grammar(&case.0);
            debug_println!("\n\n\n====== Case {} ======", i + 1);
            debug_println!("Grammar: {:?}\nWord: {}\nExpected result: {}", grammar, case.1, case.2);

            let mut earley = EarleyAlgorithm::new(grammar);
            let result = earley.check_word(case.1.to_string());
            assert_eq!(result, case.2);

            let stats = earley.get_situations_stats();
            debug_println!("Stats: {} added, {} rejected", stats.0, stats.1);
        }
    }
}
