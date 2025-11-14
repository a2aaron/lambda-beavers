use crate::debruijn::Debruijn;

pub fn reduce(term: &mut Debruijn, limit: usize) -> ReduceResult {
    for _ in 0..limit {
        let did_reduce = reduce_one(term);
        if !did_reduce {
            return ReduceResult::NormalForm;
        }
    }
    ReduceResult::NotNormalForm
}

pub enum ReduceResult {
    NormalForm,
    NotNormalForm,
}

fn reduce_one(term: &mut Debruijn) -> bool {
    let is_redex = is_redex(term);

    match term {
        Debruijn::Index(_) => false,
        Debruijn::Application { func, arg } => {
            if is_redex {
                *term = beta_reduce(func, arg);
                true
            } else {
                let reduced = reduce_one(func);
                if reduced { true } else { reduce_one(arg) }
            }
        }
        Debruijn::Abstraction { body } => reduce_one(body),
    }
}

fn is_redex(term: &Debruijn) -> bool {
    match term {
        Debruijn::Application { func, .. } => match **func {
            Debruijn::Abstraction { .. } => true,
            _ => false,
        },
        _ => false,
    }
}

fn beta_reduce(func: &Debruijn, expr: &Debruijn) -> Debruijn {
    let body = match func {
        Debruijn::Abstraction { body } => body.clone(),
        _ => panic!("Expected an abstraction"),
    };
    let term = shift_cutoff(&expr, 1);
    let subsituted = substitute(&body, &term, 1);
    let unshift = shift_cutoff(&subsituted, -1);
    unshift
}

fn substitute(term: &Debruijn, value: &Debruijn, depth: usize) -> Debruijn {
    match term {
        Debruijn::Index(term_index) => {
            if *term_index == depth {
                value.clone()
            } else {
                Debruijn::Index(*term_index)
            }
        }
        Debruijn::Application { func, arg } => {
            let func = substitute(func, value, depth);
            let arg = substitute(arg, value, depth);
            Debruijn::Application {
                func: Box::new(func),
                arg: Box::new(arg),
            }
        }
        Debruijn::Abstraction { body } => {
            let term2 = shift_cutoff(&value, 1);
            let body = substitute(body, &term2, depth + 1);
            Debruijn::Abstraction {
                body: Box::new(body),
            }
        }
    }
}

fn shift_cutoff(term: &Debruijn, amount: isize) -> Debruijn {
    _shift_cutoff(term, amount, 1)
}

fn _shift_cutoff(term: &Debruijn, amount: isize, depth: usize) -> Debruijn {
    match term {
        Debruijn::Index(index) => {
            // At depth 1
            if *index < depth {
                Debruijn::Index(*index)
            } else {
                // Recall that an index starts at 1, so if depth is set to 1
                // then this branch will always be taken.
                let index = index.checked_add_signed(amount).unwrap();
                Debruijn::Index(index)
            }
        }
        Debruijn::Application { func, arg } => {
            let func = _shift_cutoff(func, amount, depth);
            let arg = _shift_cutoff(arg, amount, depth);
            Debruijn::Application {
                func: Box::new(func),
                arg: Box::new(arg),
            }
        }
        Debruijn::Abstraction { body } => {
            // We add one to the cutoff here because we don't want to modify bound variables
            // For example, if we're at the outer-most lambda, then any Index(1)s in the lambda body
            // are referring to that lambda's bound variable and we don't modify it.
            let body = _shift_cutoff(body, amount, depth + 1);
            Debruijn::Abstraction {
                body: Box::new(body),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        debruijn::{self, Context, Debruijn, def},
        term::Classic,
    };

    use crate::reference::{beta_reduce, shift_cutoff, substitute};

    fn compile(input: &str, mut context: Context) -> Debruijn {
        let term: Classic = input.parse().unwrap();
        let term = debruijn::compile(term, &mut context).unwrap();
        term
    }

    #[test]
    fn shift_cutoff_1() {
        let term: Debruijn = 1.into();

        let expected: Debruijn = 2.into();
        let actual = shift_cutoff(&term, 1);
        assert_eq!(expected, actual);
    }

    #[test]
    fn substitute_simple() {
        let term: Debruijn = 1.into(); // λx.x
        let term2: Debruijn = 1.into(); // x

        // Make the substitution "x = x" into the term "x"
        let actual = substitute(&term, &term2, 1);
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
        let actual = substitute(&term, &term2, 1);
        // Result should be λx.x, because the inner x is shadowed
        let expected: Debruijn = def(1).into();
        assert_eq!(actual, expected);
    }
}
