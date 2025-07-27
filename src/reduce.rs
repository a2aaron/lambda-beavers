use crate::debruijn::Debruijn;

// see https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf
// and also https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture13.pdf

// ↑ n = n         if n < cutoff
//       n + up_by otherwise
// ↑ λ e = λ (↑ e) where up_by -> up_by and cutoff -> cutoff + 1
// ↑ (e1 e2) = (↑ e1) (↑ e2)

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
                Debruijn::Index(index)
            }
        }
        Debruijn::Application(func, arg) => {
            let call_func = shift_cutoff(func, up_by, cutoff);
            let call_arg = shift_cutoff(arg, up_by, cutoff);
            Debruijn::Application(Box::new(call_func), Box::new(call_arg))
        }
        Debruijn::Abstraction(func_body) => {
            // We add one to the cutoff here because we don't want to modify bound variables
            // For example, if we're at the outer-most lambda, then any Index(1)s in the lambda body
            // are referring to that lambda's bound variable and we don't modify it.
            let body = shift_cutoff(func_body, up_by, cutoff + 1);
            Debruijn::Abstraction(Box::new(body))
        }
    }
}

fn substitute(term: &Debruijn, index: usize, term2: &Debruijn) -> Debruijn {
    match term {
        Debruijn::Index(term_index) => {
            if *term_index == index {
                term2.clone()
            } else {
                Debruijn::Index(*term_index)
            }
        }
        Debruijn::Application(func, arg) => {
            let call_func = substitute(func, index, term2);
            let call_arg = substitute(arg, index, term2);
            Debruijn::Application(Box::new(call_func), Box::new(call_arg))
        }
        Debruijn::Abstraction(func_body) => {
            let term2 = up_one(&term2);
            let body = substitute(func_body, index + 1, &term2);
            Debruijn::Abstraction(Box::new(body))
        }
    }
}

/// (Note: assuming call by name semantics)
/// Let's say we are beta reducing something like this (λu.λv.u x) (a b)
/// In normal notation, what we do here is e1 {e2 / x}, which looks like the following:
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
/// (λx. e1) e2 -> e1 {e2 / x}
///
/// Where {e / x} is the substitution function, which looks like:
///
/// Substituting a literal:
/// y {e / x} = e if y == x
///             y otherwise
/// change literal y into term e if y is the literal being subtituted, otherwise leave it alone
/// ex: y {λx.x / y} = λx.x
/// ex: a {λx.x / b} = a
///
/// Substituting an application
/// (e1 e2) {e / x} = (e1 {e / x}  e2 {e / x})
/// this one is simple, just recurse into the function and argument
///
/// Substituting an abstraction
/// (λy.e1) {e / x} = λy.e1 {e / x} where y != x and y is not in fv(e)
/// (where fv(e) means "the set of free variables of e")
/// Those last two conditionals are important! The first means that we only
/// substitute a literal in e1 if that literally is not being captured by the lambda (in this case, y)
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
/// not already a free variable in the substituted expression
/// (in other words, all variables in the expression are assumed to be free with respect to the lambda,
/// which makes sense! that expression came from outside the lambda anyways, so there's no way any
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
/// N {e / M} = e if N == M
///             N otherwise
/// (basically the same)
///
/// Substituting an abstraction:
/// (e1 e2) {e / M} = (e1 {e / M}  e2 {e / M})
/// (basically the same)
///
/// Substituting an abstraction
/// (λ e1) {e / M} = λ e1 {up_one(e) / M + 1}
///
/// For this one, when we recurse into e1, all of the variables we care about replacing
/// are going to be one higher now, and we need to also bump up every variable in our substited
/// expression by one to compensate for the depth
///
/// Note that up_one only modifies free varaibles within it's argument. This means that it won't
/// modify anything whose index is equal to or lower than it's depth. See shift_cutoff for
/// implementation.
///
/// Finally, to complete the beta-reduction, we need to take the body of our substituted expression
/// and extract it from the lambda--this will drop every index in the term down by one.
///
/// Hence, the final rule for beta reduction will look like:
/// (λ e1) e2 = down_one(e1 {up_one(e) / 1})
pub fn beta_reduce(func: &Debruijn, expr: &Debruijn) -> Debruijn {
    let body = match func {
        Debruijn::Abstraction(body) => body.clone(),
        _ => panic!("Expected an abstraction"),
    };
    let term = up_one(&expr);
    let subsituted = substitute(&body, 1, &term);
    let unshift = down_one(&subsituted);
    unshift
}

#[cfg(test)]
mod tests {

    use crate::{
        debruijn::{self, def, Context, Debruijn},
        reduce::{beta_reduce, shift_cutoff, substitute},
        term::Term,
    };

    fn compile(input: &str, mut context: Context) -> Debruijn {
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
        let actual = substitute(&term, 1, &term2);
        // Just "x"
        let expected: Debruijn = 1.into();
        assert_eq!(actual, expected);
    }

    #[test]
    fn substitute_less_trivial() {
        // (λx.λy.λz x y z) w

        let mut context = Context::default();
        context.push_literal("w");

        let func_body = compile("λx.λy.λz. x y z", context.clone());
        assert_eq!(func_body, def(def(def(((3, 2), 1)))));

        let term: Debruijn = compile("w", context.clone());
        assert_eq!(term, 1.into());

        // beta reduce the term "(λx.λy.λz x y z) w"
        let actual = beta_reduce(&func_body, &term);
        // Result should be λw.λx.λy.λz. w y z
        let expected: Debruijn = compile("λy.λz. w y z", context);
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
        let term = compile("λu.λv.u x", context.clone());
        assert_eq!(term, def(def((2, 3)))); // λu.λv.u x = λ λ 2 3

        let term2 = compile("y", context.clone());
        assert_eq!(term2, 2.into()); // y = 2

        // beta reduec the term "λx.(λu.λv.u x) y"
        let actual = beta_reduce(&term, &term2);

        // Result should be λv.y x (full context is λy.λx.(λv.y x))
        let expected = compile("λv.y x", context.clone());

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
        let actual = substitute(&term, 1, &term2);
        // Result should be λx.x, because the inner x is shadowed
        let expected: Debruijn = def(1).into();
        assert_eq!(actual, expected);
    }
}
