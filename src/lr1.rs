use std::collections::{HashMap, VecDeque};
use std::fmt::{Debug, Display, Formatter};
use std::fmt::Write;
use std::iter::Peekable;
use std::rc::Rc;
use std::sync::Arc;

use debug_print::debug_println;
use fnv::{FnvHashMap, FnvHashSet};

use {crate::ALGO_END, crate::ALGO_START, crate::EPSILON, crate::Rule};

use crate::Parser;

#[derive(Clone, Eq, Hash, PartialEq)]
struct Situation {
    rule: Arc<Rule>,

    // \in [0, |w|]
    dot_index: usize,

    next: char,
}

impl Situation {
    /// Возвращает символ сразу после точки
    /// В силу особенностей char в rust, асимптотика `O(|rule.alpha|)`.
    pub fn dot_term(&self) -> char {
        self.rule.alpha.chars().nth(self.dot_index).unwrap_or(EPSILON)
    }
}

impl Debug for Situation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}→{}•{}, {})", self.rule.A, &self.rule.alpha[..self.dot_index], &self.rule.alpha[self.dot_index..],
               self.next)
    }
}

/// Упрощенная функция для проверки символа на терминальность.
/// Пользуемся тем фактом, что все нетерминальные символы -- заглавные буквы, и что третьей категории символов нет.
fn is_terminal(u: char) -> bool {
    !u.is_uppercase() || u == ALGO_START || u == ALGO_END
}

/// Структура для предпосчитанного множества `{ First(u) | u ∈ Ν }`
#[derive(Default)]
struct CachedFirst {
    table: FnvHashMap<char, FnvHashSet<char>>,
}

impl CachedFirst {
    /// Конструирует CachedFirst из правил грамматики.
    ///
    /// Функция пробегается по правилам и добавляет в таблицу те значения `First(rule.A)`, которые может посчитать
    /// за не более одно обращение к `self.table`. Цикл по всем правилам продолжается до тех пор, пока `table` меняется.
    /// Внешний цикл нужен, поскольку `First` может транзитивно раскрывать нетерминалы по данным правилам, пока не
    /// получит терминал.
    ///
    /// `self.table` в конце концов перестанет меняться (сойдется), потому что содержит неповторяющиеся терминалы,
    /// которых конечное количество в грамматике.
    pub fn from_grammar(grammar: &Vec<Rule>) -> Self {
        let mut res = Self::default();

        loop {
            let mut changed = false;
            for rule in grammar {
                if let Some(first) = rule.alpha.chars().next() {
                    if is_terminal(first) {
                        // Нашли терминал
                        changed |= res.table.entry(rule.A).or_default().insert(first);
                    } else if let Some(transitive_first) = res.table.get(&first).cloned() {
                        #[allow(non_snake_case)] let entry_A = res.table.entry(rule.A).or_default();
                        // Нашли нетерминал
                        let init_len = entry_A.len();
                        entry_A.extend(transitive_first);
                        changed |= init_len != entry_A.len();
                    }
                } else {
                    // Нашли эпсилон
                    changed |= res.table.entry(rule.A).or_default().insert(EPSILON);
                }
            }

            if !changed {
                break;
            }
        }

        res
    }

    /// Считает `First(alpha)`.
    ///
    /// Асимптотика: `O(|α| * |Σ|)`. В худшем случае `α` состоит из нетерминалов, каждый из которых раскрывается вместе
    /// с `ε`.
    pub fn get(&self, alpha: &str) -> FnvHashSet<char> {
        let mut res = FnvHashSet::default();

        for curr_char in alpha.chars() {
            let mut terminate = true;
            if is_terminal(curr_char) {
                res.insert(curr_char);
            } else {
                let firsts_for_nonterminal = self.table.get(&curr_char)
                    .expect(&*format!("CachedFirst is not prepared for {}", curr_char));
                res.extend(firsts_for_nonterminal);
                if firsts_for_nonterminal.contains(&EPSILON) {
                    terminate = false;
                }
            }

            if terminate {
                break;
            }
        }

        res.remove(&EPSILON);
        res
    }
}

/// В грамматике LR1 есть действия shift и reduce.
/// В моем случае я оставляю только одну таблицу (вместо двух), поэтому я добавляю новое действие -- переход по
/// нетерминальному символу, которое требуется в конце Reduce.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Action {
    Shift(usize),
    Reduce(Arc<Rule>),
    NonterminalGoto(usize),
}

/// Скомпилированная грамматика LR1
pub struct LRGrammar {
    actions: Vec<FnvHashMap<char, Action>>,
}

/// Единственно возможная ошибка построения таблицы грамматики -- конфликт в таблице
pub struct LR1Conflict {
    vertex_id: usize,
    letter: char,
    action1: Action,
    action2: Action,
}

impl Display for LR1Conflict {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "LR1Conflict in vertex {} at {}: {:?}/{:?}", self.vertex_id, self.letter, self.action1, self.action2)
    }
}

/// Структура создается для компиляции грамматики
pub struct LRGrammarBuilder {
    grammar_map: FnvHashMap<char, Vec<Arc<Rule>>>,
    first_operator: CachedFirst,
    vertices_automaton: HashMap<Rc<Vec<Situation>>, usize>,
    actions: Vec<FnvHashMap<char, Action>>,
}

impl LRGrammarBuilder {
    pub fn from_grammar(grammar: Vec<Rule>) -> Self {
        let first_operator = CachedFirst::from_grammar(&grammar);

        let mut grammar_map = FnvHashMap::<char, Vec<Arc<Rule>>>::default();
        grammar_map.insert(ALGO_START, vec![Arc::new(Rule { A: ALGO_START, alpha: "S".to_string() })]);
        for rule in grammar {
            grammar_map.entry(rule.A).or_default().push(Arc::new(rule));
        }

        Self {
            grammar_map,
            first_operator,
            vertices_automaton: HashMap::new(),
            actions: Vec::new(),
        }
    }

    /// Генерирует `CLOSURE(situations)` и создает вершину с замыканием этих ситуаций, если она еще не существует.
    /// Возвращает номер вершины, `CLOSURE(situations)` и индикатор, была ли фактически создана новая вершина.
    fn make_closure_vertex(&mut self, mut situations: Vec<Situation>) -> (usize, Rc<Vec<Situation>>, bool) {
        let mut range_changed = 0..situations.len();
        while !range_changed.is_empty() {
            let iteration_sit_size = situations.len();

            for sit_ind in range_changed {
                let new_sit = &situations[sit_ind];
                let dot_char = new_sit.dot_term();
                if let Some(replacements) = self.grammar_map.get(&dot_char) {
                    let first_arg = format!(
                        "{}{}", new_sit.rule.alpha[(new_sit.dot_index + 1)..].to_string(), new_sit.next);

                    for next_term in self.first_operator.get(first_arg.as_str()) {
                        // ... \forall \in First(first_arg)
                        for next_rule in replacements {
                            // ... \forall \in { rule \in grammar | rule := dot_char -> <...> }
                            let sit = Situation { rule: next_rule.clone(), dot_index: 0, next: next_term };
                            if situations.iter().find(|&exist_sit| &sit == exist_sit).is_none() {
                                situations.push(sit);
                            }
                        }
                    }
                }
            }

            // нужно обработать только новые ситуации
            range_changed = iteration_sit_size..situations.len();
        }

        // Ситуации раскрыты по замыканию, фиксируем их в Rc
        let situations = Rc::new(situations);

        if let Some(id) = self.vertices_automaton.get(&situations) {
            // Вершина уже добавлена
            (*id, situations, false)
        } else {
            // Новая вершина
            let id = self.vertices_automaton.len();
            self.vertices_automaton.insert(situations.clone(), id);
            self.actions.push(FnvHashMap::default());
            (id, situations, true)
        }
    }

    /// Добавляет стрелку с действием в автомат
    /// Возвращает LR1Conflict, если из вершины `id` по символу `letter` уже добавлено *иное* действие.
    fn add_action(&mut self, id: usize, letter: char, action: Action) -> Result<(), LR1Conflict> {
        debug_println!("Arrow from {} by {} action {:?}", id, letter, action);
        self.actions[id].insert(letter, action.clone()).map_or(Ok(()), |old_value| -> Result<(), LR1Conflict> {
            if old_value != action {
                debug_println!("GRAPHVIZ VIEW\n{}\n\n", self.to_graphviz());
                Err(LR1Conflict { vertex_id: id, letter, action1: old_value, action2: action })
            } else {
                Ok(())
            }
        })
    }

    /// Полностью заполняет таблицу actions. Или возвращает конфликт.
    pub fn build_grammar(&mut self) -> Result<(), LR1Conflict> {
        let init_situation = vec![Situation {
            rule: self.grammar_map[&ALGO_START].first().unwrap().clone(),
            dot_index: 0,
            next: ALGO_END,
        }];
        let (id, init_situation, _) = self.make_closure_vertex(init_situation);

        let mut vertices_queue = VecDeque::from(vec![(id, init_situation)]);

        while !vertices_queue.is_empty() {
            let (id, situations) = vertices_queue.pop_front().unwrap();
            let mut shift_situations = FnvHashMap::<char, Vec<Situation>>::default();

            for sit in &*situations {
                if sit.dot_index == sit.rule.alpha.len() {
                    // Reduce
                    self.add_action(id, sit.next, Action::Reduce(sit.rule.clone()))?;
                } else {
                    // Shift
                    let next_term = sit.dot_term();
                    let next_sit = Situation { rule: sit.rule.clone(), dot_index: sit.dot_index + 1, next: sit.next };
                    shift_situations.entry(next_term).or_default().push(next_sit);
                }
            }

            for (letter, base_situations) in shift_situations {
                let (next_id, next_situations, vertex_new) = self.make_closure_vertex(base_situations);
                let action = if is_terminal(letter) { Action::Shift(next_id) } else { Action::NonterminalGoto(next_id) };
                self.add_action(id, letter, action)?;
                if vertex_new {
                    vertices_queue.push_back((next_id, next_situations));
                }
            }
        }

        debug_println!("{}", self.to_graphviz());
        Ok(())
    }

    /// Создает LRGrammar из сгенерированной таблицы
    pub fn make(self) -> LRGrammar {
        LRGrammar { actions: self.actions }
    }

    /// Рисует self.actions в graphviz
    pub fn to_graphviz(&self) -> String {
        let mut invisible_vertex_id = 0;
        let mut make_invisible_vertex = |output: &mut String| {
            let id = invisible_vertex_id;
            invisible_vertex_id += 1;

            writeln!(
                output,
                "__invis_node_{} [label=\"\",shape=none,height=.0,width=.0]", id
            ).unwrap();

            format!("__invis_node_{}", id)
        };

        let mut output = String::new();
        writeln!(output, "digraph {{").unwrap();

        let entry_node = make_invisible_vertex(&mut output);
        writeln!(output, "{} -> 0", entry_node).unwrap();

        for (i, vertex) in self.actions.iter().enumerate() {
            let mut label = format!("{}\n", i);
            for situation in &**self.vertices_automaton.iter().find(|(_, &v)| v == i).unwrap().0 {
                writeln!(label, "{:?}", situation).unwrap();
            }
            writeln!(output, "{} [label=\"{}\",shape=box,fontname=\"monospace\"]", i, label.escape_debug()).unwrap();
            for (letter, action) in vertex {
                let (next_id, label) = match action {
                    Action::Shift(id) => (id.to_string(), format!("Shift({})", letter)),
                    Action::NonterminalGoto(id) => (id.to_string(), format!("NTGoto({})", letter)),
                    Action::Reduce(rule) =>
                        (make_invisible_vertex(&mut output), format!("Reduce({}; {:?})", letter, rule)),
                };
                writeln!(output, "{} -> {} [label=\"{}\"]", i, next_id, label.escape_debug()).unwrap();
            }
        }

        writeln!(output, "}}").unwrap();
        output
    }
}

pub fn make_lr1_parser(grammar: Vec<Rule>) -> Result<Box<dyn Parser>, String> {
    let mut builder = LRGrammarBuilder::from_grammar(grammar);
    if let Err(conflict) = builder.build_grammar() {
        Err(conflict.to_string())
    } else {
        Ok(Box::new(builder.make()))
    }
}

impl Parser for LRGrammar {
    /// Проверяет, находится ли слово в грамматике
    fn contains(&self, word: &str) -> bool {
        let end_rule = Rule { A: ALGO_START, alpha: "S".to_string() };
        let mut word_it = word.chars().peekable();
        let mut vertex_stack: Vec<usize> = vec![0];

        let get_look_ahead_term = |x: &mut Peekable<std::str::Chars>| -> char {
            *x.peek().unwrap_or(&ALGO_END)
        };
        let get_current_vertex_id = |x: &mut Vec<usize>| -> usize {
            *x.last().expect("Should always have vertex id")
        };
        let get_action = |vertex_id: usize, letter: char| -> Option<&Action> {
            self.actions.get(vertex_id)
                .expect(format!("Vertex {} does not exist", vertex_id).as_str())
                .get(&letter)
        };

        loop {
            let vertex_id = get_current_vertex_id(&mut vertex_stack);
            let forward_term = get_look_ahead_term(&mut word_it);
            let action = get_action(vertex_id, forward_term);
            if action.is_none() {
                debug_println!("No action in {} for {}, decline", vertex_id, forward_term);
                return false;
            }

            match action.unwrap() {
                Action::Shift(next_id) => {
                    word_it.next();
                    vertex_stack.push(*next_id);
                }

                Action::NonterminalGoto(_) => { panic!("Got NTGoto in {} by {}", vertex_id, forward_term) }

                Action::Reduce(rule) => {
                    if **rule == end_rule {
                        return true;
                    }

                    let vertices_exclude_len = rule.alpha.chars().count();
                    if vertices_exclude_len + 1 > vertex_stack.len() {
                        panic!("Not enough vertices in stack for {:?} in {} by {}", rule, vertex_id, forward_term);
                    }
                    vertex_stack.drain((vertex_stack.len() - vertices_exclude_len)..);

                    let vertex_id = get_current_vertex_id(&mut vertex_stack);
                    let forward_term = rule.A;
                    let reduce_action = get_action(vertex_id, forward_term)
                        .expect(format!("No action for {:?} in {} by {}",
                                        action.unwrap(), vertex_id, forward_term).as_str());

                    if let Action::NonterminalGoto(next_id) = reduce_action {
                        vertex_stack.push(*next_id);
                    } else {
                        panic!("Action after Reduce is not NTGoto, but {:?}", reduce_action);
                    }
                }
            }
        }
    }
}