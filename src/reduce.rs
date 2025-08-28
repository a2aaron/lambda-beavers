use std::{fmt::Display, rc::Rc};

use clap::ValueEnum;

use crate::{
    debruijn::{Debruijn, call, def, idx},
    graph::{NodeIndex, ReductionGraph},
    replace::VisitOrder,
    utils::Rng,
};

// see https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf
// and also https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture13.pdf

/// (Note: assuming call by name semantics)
/// Let's say we are beta reducing something like this (λu.λv.u x) (a b)
/// In normal notation, what we do here is t1 {t2 / x}, which looks like the following:
/// λu.λv.u x | initial term
/// λu.λv.u x | replace all instances of x by (a b)
/// λu.λv.u (a b)
///
/// Note that we do respect variable shadowing--we only replace the variable if it is free (ie: not
/// bound in the term). For example, in reducing (λy.(λx.x λx.z) x) a, we would get
/// λy.(λx.x λx.z) x | initial term
/// λy.(λx.x λx.z) a | replace all *free* instances of x with a
/// In λx.x λx.z, the x is bound and is not free so we do not replace it
///
/// The overall procedure therefore, would look something like this:
/// (λx. t1) t2 -> t1 {t2 / x}
///
/// Where {t / x} is the substitution function, which looks like:
///
/// Substituting a literal:
/// y {t / x} = t if y == x
///             y otherwise
/// change literal y into term t if y is the literal being subtituted, otherwise leave it alone
/// ex: y {λx.x / y} = λx.x
/// ex: a {λx.x / b} = a
///
/// Substituting an application
/// (t1 t2) {t / x} = (t1 {t / x}  t2 {t / x})
/// this one is simple, just recurse into the function and argument
///
/// Substituting an abstraction
/// (λy.t1) {t / x} = λy.t1 {t / x} where y != x and y is not in fv(t)
/// (where fv(t) means "the set of free variables of t")
/// Those last two conditionals are important! The first means that we only
/// substitute a literal in t1 if that literally is not being captured by the lambda (in this case, y)
///
/// so for example, (λa.x (λx.x)) {y / x}
/// = (λa.y (λx.x))
/// We do not substitute for the inner x because it's been bound to that inner λx
///
/// The second means that we don't allow name collisions.
/// For example, what should the result of (λy.x) {y / x} be?
/// We can substitute x, it's not bound to the λy at all, but we probably don't want to
/// substitute y for x as a *name*--y is bound. What we want it to be is is for those Ys to be distinct
/// eg: we would rather write (λy1.x) {y2 / x} = λy1.y2
/// Fortunately, we can always rename variables so that this works out. That's what this second
/// condition is doing--it's just ensuring that when we substitute, the argument of the lambda is
/// not already a free variable in the substituted term
/// (in other words, all variables in the term are assumed to be free with respect to the lambda,
/// which makes sense! that term came from outside the lambda anyways, so there's no way any
/// of them are already bound)
///
/// Finally to actually do our beta-reduction, we just drop out the outermost lambda that we subtituted
/// into. For example, in (λy.(λx.x λx.z) x) a, we had computed this substitution
/// λy.(λx.x λx.z) x {y / a} = λy.(λx.x λx.z) a
/// so our final term would just be λy.(λx.x λx.z) a (we drop the outer λy along with the a)
///
/// Alright. Cool, how do we translate this to Debruijn indicies?
///
/// Recall that our notation is using 1-indexed values, so λx.x = λ 1, not λ 0
/// A free variable in this notation is any index whose value would take it "outside" the current
/// term. This basically means that if the value for some index is greater than the current
/// depth it's in, then it's a free variable
///
/// ex: λa.λx.a = λ λ 2. If we just look at that inner fragement, λx.a, and assume that a remains in
/// the outer context like before, then we get λx.a = λ 2. Notice how 2 is greater than it's current
/// depth (if it would bound it would need to be 1).
///
/// Without the context, we won't know which specific value that the unbound a would be indexed as
/// eg: we could also have λa.λb.λx.a = λ λ λ 3, and now suddently our λx.a fragment looks like λ 3,
/// so the context matters here a lot.
///
/// First let's tackle substitution. It'll be very similar to normal substitution, but with two caveats
/// 1. we don't need to worry about the whole variable renaming thing in the lambda-branch! all the
/// variables are guarenteed to be "differently named"/unambigious to which lambda/outer context they
/// are bound to!
///
/// 2. we DO need to worry about indicies changing as a result of values becoming more nested
/// Recall that the depth of a variable means it will have a different index. eg: we have,
/// λx.x λa.x λb.x λc.x = λ 1 λ 2 λ 3 λ 4
/// All of those Xes refer to the same variable, but get different indicies due to being more deeply
/// nested.
///
/// So that means for our substitution operation, it needs to look like this:
///
/// Substituting a literal:
/// N {t / M} = t if N == M
///             N otherwise
/// (basically the same)
///
/// Substituting an abstraction:
/// (t1 t2) {t / M} = (t1 {t / M}  t2 {t / M})
/// (basically the same)
///
/// Substituting an abstraction
/// (λ t1) {t / M} = λ t1 {up_one(t) / M + 1}
///
/// For this one, when we recurse into t1, all of the variables we care about replacing
/// are going to be one higher now, and we need to also bump up every variable in our substited
/// term by one to compensate for the depth
///
/// Note that up_one only modifies free varaibles within it's argument. This means that it won't
/// modify anything whose index is equal to or lower than it's depth. See shift_cutoff for
/// implementation.
///
/// Finally, to complete the beta-reduction, we need to take the body of our substituted term
/// and extract it from the lambda--this will drop every index in the term down by one.
///
/// Hence, the final rule for beta reduction will look like:
/// (λ t1) t2 = down_one(t1 {up_one(t) / 1})

pub enum ReductionResult {
    NormalForm(Debruijn),
    Irreducible,
    MaxReductionsReached,
}

impl Display for ReductionResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReductionResult::NormalForm(term) => write!(f, "Normal Form: {}", term),
            ReductionResult::Irreducible => write!(f, "Irreducible"),
            ReductionResult::MaxReductionsReached => write!(f, "Max Reductions Reached"),
        }
    }
}

pub fn reduce(
    term: &Debruijn,
    reduction_strategy: &mut ReductionStrategy,
    visit_order: VisitOrder,
    max_reductions: usize,
) -> (ReductionResult, usize) {
    let mut graph = ReductionGraph::with_root(term.clone(), visit_order);
    for i in 0..max_reductions {
        if let Some(value) = reduce_one(reduction_strategy, &mut graph) {
            return (value, i);
        }
    }
    (ReductionResult::MaxReductionsReached, max_reductions)
}

pub fn reduce_one(
    reduction_strategy: &mut ReductionStrategy,
    graph: &mut ReductionGraph,
) -> Option<ReductionResult> {
    if let Some((reduced_term, _)) = graph.bnf() {
        return Some(ReductionResult::NormalForm(
            reduced_term.term.as_ref().clone(),
        ));
    }

    let node_to_reduce = reduction_strategy.get_node(graph);
    match node_to_reduce {
        Some(node_to_reduce) => {
            let reduction_node = graph.get(node_to_reduce).unwrap();
            let redex_index = reduction_node.unevaluated_redexes[0];
            graph.reduce_node(node_to_reduce, redex_index);
        }
        _ => return Some(ReductionResult::Irreducible),
    }

    None
}

pub enum ReductionStrategy {
    DFS,
    BFS,
    Random(Rng),
}

impl ReductionStrategy {
    pub fn get_node(&mut self, graph: &mut ReductionGraph) -> Option<NodeIndex> {
        if !graph.any_reducible() {
            return None;
        }
        let node = match self {
            ReductionStrategy::DFS => graph.incomplete_nodes[graph.incomplete_nodes.len() - 1],
            ReductionStrategy::BFS => graph.incomplete_nodes[0],
            ReductionStrategy::Random(rng) => {
                let index = rng.rand_usize() % graph.incomplete_nodes.len();
                graph.incomplete_nodes[index]
            }
        };
        Some(node)
    }

    pub fn random() -> ReductionStrategy {
        ReductionStrategy::Random(Rng::new())
    }
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum ReductionStrategyKind {
    DFS,
    BFS,
    Random,
}

impl From<ReductionStrategyKind> for ReductionStrategy {
    fn from(value: ReductionStrategyKind) -> Self {
        match value {
            ReductionStrategyKind::DFS => ReductionStrategy::DFS,
            ReductionStrategyKind::BFS => ReductionStrategy::BFS,
            ReductionStrategyKind::Random => ReductionStrategy::random(),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Fragment<'a>(pub &'a Debruijn);

impl<'a> Display for Fragment<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn beta_reduce(redex: &Debruijn) -> Debruijn {
    match redex {
        Debruijn::Application { func, arg } => _beta_reduce(&func, &arg),
        _ => panic!("Expected an application, got {redex}"),
    }
}

fn _beta_reduce(func: &Debruijn, arg: &Debruijn) -> Debruijn {
    match func {
        Debruijn::Abstraction { body } => __beta_reduce(&body, arg),
        _ => panic!("Expected an abstraction, got {func}"),
    }
}

fn __beta_reduce(body: &Debruijn, arg: &Debruijn) -> Debruijn {
    let term = up_one(&arg);
    let subsituted = substitute(&body, &term);
    let unshift = down_one(&subsituted);
    unshift
}

fn substitute(function_body: &Debruijn, replacer: &Debruijn) -> Debruijn {
    // This tries to substitute indicies that point to the implicit lambda that `function_body` is
    // part of.
    // Consider, for example, where we want to subsitute into λ 0 1 2, sow e have function body = 0 1 2.
    // in this case, 0 would be replaced by `replacer`. Note that we need to track depth, so the index
    // we match on (the `match_index`) will go up by one every time we go into a nested abstraction.
    // For example: In λ 0 λ 1 λ 2 (so `function_body` = 0 λ 1 λ 2), we'd substitute `replacer`
    // into 0, 1, and 2.
    // Also note that when we recurse into a nested abstraction, we also must bump up the indicies for
    // any free variables in `replacer` by one to accomodate for the fact that those need to point over
    // additional lambdas. Hence the replacer_up_by goes up by one as well.
    fn _substitute(
        function_body: &mut Debruijn,
        match_index: usize,
        replacer: &Debruijn,
        replacer_up_by: usize,
    ) {
        match function_body {
            Debruijn::Index(term_index) => {
                if *term_index == match_index {
                    let replacer = up_by(replacer, replacer_up_by);
                    *function_body = replacer.clone()
                }
            }
            Debruijn::Application { func, arg } => {
                _substitute(Rc::make_mut(func), match_index, replacer, replacer_up_by);
                _substitute(Rc::make_mut(arg), match_index, replacer, replacer_up_by);
            }
            Debruijn::Abstraction { body } => {
                _substitute(
                    Rc::make_mut(body),
                    match_index + 1,
                    &replacer,
                    replacer_up_by + 1,
                );
            }
        }
    }
    let mut term = function_body.clone();
    _substitute(&mut term, 1, &replacer, 0);
    term
}

fn up_by(term: &Debruijn, up_by: usize) -> Debruijn {
    shift_cutoff(term, up_by as isize, 1)
}

// ↑ n = n         if n < cutoff
//       n + up_by otherwise
// ↑ λ t = λ (↑ t) where up_by -> up_by and cutoff -> cutoff + 1
// ↑ (t1 t2) = (↑ t1) (↑ t2)
fn up_one(term: &Debruijn) -> Debruijn {
    shift_cutoff(term, 1, 1)
}

fn down_one(term: &Debruijn) -> Debruijn {
    shift_cutoff(term, -1, 1)
}

/// Shift the indicies for all terms up by an amount. Indicies below the cutoff are not modified
/// This is useful during beta reduction because we need to "drop out" an abstraction.
fn shift_cutoff(term: &Debruijn, up_by: isize, cutoff: usize) -> Debruijn {
    match term {
        Debruijn::Index(term_index) => {
            if *term_index < cutoff {
                Debruijn::Index(*term_index)
            } else {
                // Recall that an index starts at 1, so if cutoff is set to 1, then this branch
                // will always be taken.
                let index = term_index.checked_add_signed(up_by).unwrap();
                idx(index)
            }
        }
        Debruijn::Application { func, arg } => {
            let call_func = shift_cutoff(func, up_by, cutoff);
            let call_arg = shift_cutoff(arg, up_by, cutoff);
            call(call_func, call_arg)
        }
        Debruijn::Abstraction { body } => {
            // We add one to the cutoff here because we don't want to modify bound variables
            // For example, if we're at the outer-most lambda, then any Index(1)s in the lambda body
            // are referring to that lambda's bound variable and we don't modify it.
            let body = shift_cutoff(body, up_by, cutoff + 1);
            def(body)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        debruijn::{self, Context, Debruijn, call, def},
        reduce::{_beta_reduce, shift_cutoff, substitute},
        term::Term,
    };

    fn beta_reduce(term: &Debruijn) -> Debruijn {
        match term {
            Debruijn::Application { func, arg } => _beta_reduce(func, arg),
            _ => panic!("Expected an application"),
        }
    }

    fn compile(input: &str) -> Debruijn {
        _compile(input, Context::default())
    }

    fn _compile(input: &str, mut context: Context) -> Debruijn {
        let term: Term = input.parse().unwrap();
        let term = debruijn::compile(term, &mut context).unwrap();
        term
    }

    #[test]
    fn shift_cutoff_1() {
        let term: Debruijn = 1.into();

        let expected: Debruijn = 2.into();
        let actual = shift_cutoff(&term, 1, 1);
        assert_eq!(expected, actual);
    }

    #[test]
    fn substitute_simple() {
        let term: Debruijn = 1.into(); // λx.x
        let term2: Debruijn = 1.into(); // x

        // Make the substitution "x = x" into the term "x"
        let actual = substitute(&term, &term2);
        // Just "x"
        let expected: Debruijn = 1.into();
        assert_eq!(actual, expected);
    }

    #[test]
    fn substitute_less_trivial() {
        // (λx.λy.λz x y z) w

        let mut context = Context::default();
        context.push_literal("w");

        let func_body = _compile("λx.λy.λz. x y z", context.clone());
        assert_eq!(func_body, def(def(def(((3, 2), 1)))));

        let term: Debruijn = _compile("w", context.clone());
        assert_eq!(term, 1.into());

        // beta reduce the term "(λx.λy.λz x y z) w"
        let actual = _beta_reduce(&func_body, &term);
        // Result should be λw.λx.λy.λz. w y z
        let expected: Debruijn = _compile("λy.λz. w y z", context);
        assert_eq!(expected, def(def(((3, 2), 1))));
        println!("{}", actual);
        println!("{}", expected);

        assert_eq!(actual, expected);
    }

    #[test]
    fn beta_reduce_example() {
        // λy.λx.(λu.λv.u x) y -> λ λ (λ λ 2 3) 2
        let mut context = Context::default();
        context.push_literal("y");
        context.push_literal("x");
        let term = _compile("λu.λv.u x", context.clone());
        assert_eq!(term, def(def((2, 3)))); // λu.λv.u x = λ λ 2 3

        let term2 = _compile("y", context.clone());
        assert_eq!(term2, 2.into()); // y = 2

        // beta reduec the term "λx.(λu.λv.u x) y"
        let actual = _beta_reduce(&term, &term2);

        // Result should be λv.y x (full context is λy.λx.(λv.y x))
        let expected = _compile("λv.y x", context.clone());

        println!("{} {}", term, term2);
        println!("{}", actual);
        println!("{}", expected);
        assert_eq!(expected, def((3, 2)));
        assert_eq!(actual, expected);
    }

    #[test]
    fn substitute_shadowing() {
        let term: Debruijn = def(1); // λx.x
        let term2: Debruijn = 1.into(); // x

        // Make the substitution "x = x" into the term "λx.x"
        let actual = substitute(&term, &term2);
        // Result should be λx.x, because the inner x is shadowed
        let expected: Debruijn = def(1).into();
        assert_eq!(actual, expected);
    }

    #[test]
    fn beta_reduce_and_false() {
        let term = compile("(λp.λq.p q p) (λx.λy.y)");
        assert_eq!(term, call(def(def(((2, 1), 2))), def(def(1))));
        let actual = beta_reduce(&term);
        let expected = compile("λq.(λy. λx. x) q (λy. λx. x)");
        assert_eq!(expected, def(((def(def(1)), 1), def(def(1)))));
        assert_eq!(actual, expected);
    }

    #[test]
    fn beta_reduce_and_false_2() {
        let ctx = Context::from(["q"]);
        let term = _compile("(λy. λx. x) q", ctx);
        assert_eq!(term, call(def(def(1)), 1));
        let actual = beta_reduce(&term);
        let expected = compile("λx. x");
        assert_eq!(actual, expected);
    }

    #[test]
    fn beta_reduce_succ() {
        let succ = compile("λn.λf.λx.f (n f x)");
        assert_eq!(succ, def(def(def((2, ((3, 2), 1))))));
        let zero = compile("λf.λx.x");
        assert_eq!(zero, def(def(1)));

        let expected = compile("λf.λx.f ((λg.λy.y) f x)");
        assert_eq!(expected, def(def((2, (((def(def(1)), 2), 1))))));

        let actual = _beta_reduce(&succ, &zero);
        assert_eq!(expected, actual)
    }
}
