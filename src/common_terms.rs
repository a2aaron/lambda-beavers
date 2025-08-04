#![allow(non_snake_case)]

use crate::debruijn::{self, Debruijn, call, def, idx};

macro_rules! define_term {
    ($name:ident, $value:expr) => {
        #[allow(dead_code)]
        fn ${concat($name, _STR)}() -> String { $value.to_string() }

        pub fn $name() -> Debruijn {
            Debruijn::from($value)
        }
    };
}

define_term!(IDENT, "λx.x");

define_term!(TRUE, "λx.λy.x");
define_term!(FALSE, "λx.λy.x");

define_term!(AND, "λp.λq.p q p");
define_term!(OR, "λp.λq.p p q");

define_term!(NOT, format!("λx.λy.x ({}) ({})", TRUE_STR(), FALSE_STR()));

define_term!(SUCC, "λn.λf.λx.f (n f x)");
define_term!(PLUS, "λm.λn.λf.λx.m f (n f x)");
define_term!(PLUS_2, format!("λm.λn.m ({}) n", SUCC_STR()));
define_term!(MULT, "λm.λn.λf.m (n f)");
define_term!(
    MULT_2,
    format!("λm.λn.m (({}) n) ({})", PLUS_STR(), CHURCH_STR(0))
);
define_term!(POW, "λb.λn.n b");
define_term!(
    POW_2,
    format!("λb.λn.n (({}) b) ({})", MULT_STR(), CHURCH_STR(1))
);
define_term!(POW_3, "λb.λn.λf.n b f");

fn CHURCH_STR(nat: usize) -> String {
    if nat == 0 {
        "λf.λx.x".to_string()
    } else {
        let opening_parens = "(f".repeat(nat - 1);
        let closing_parens = ")".repeat(nat - 1);
        format!("λf.λx.f {} x{}", opening_parens, closing_parens)
    }
}

pub fn CHURCH(nat: usize) -> Debruijn {
    let mut inner = idx(1);
    for _ in 0..nat {
        inner = call(idx(2), inner);
    }
    def(def(inner))
}

fn from_church(term: &Debruijn) -> Option<usize> {
    fn from_church_body(term: &Debruijn) -> Option<usize> {
        // Base case, this is the base case where the body is just Index(1)
        if *term == debruijn::idx(1) {
            return Some(0);
        }
        // Otherwise, we expect the term to be an application whose left-hand is Index(2) and whose
        // right hand is a church numeral body
        if let Debruijn::Application { func, arg } = term {
            if **func != debruijn::idx(2) {
                return None;
            }

            if let Some(church_number) = from_church_body(arg) {
                return Some(church_number + 1);
            } else {
                return None;
            }
        }

        // Otherwise, this isn't a church numeral
        None
    }
    // A church numeral looks like this: λf.λx.f (f (f (f x)))
    // (Or in Debruijn notation, like this: λ λ 2 (2 (2 (2 1)))
    // Which is a two argument function that takes f and x and then applies f to x N times
    // This means we expect two abstractions followed by a series of right-recursive applications
    // whose left-hand (function) is an Index(2) and whose final right-hand (argument) is an Index(1)
    if let Debruijn::Abstraction { body } = term
        && let Debruijn::Abstraction { body } = &**body
    {
        from_church_body(&body)
    } else {
        None
    }
}

pub fn to_string(term: &Debruijn) -> String {
    if let Some(church_number) = from_church(term) {
        return format!("CHURCH_{}", church_number.to_string());
    }

    let definitions = [
        (IDENT(), "IDENT"),
        (TRUE(), "TRUE"),
        (FALSE(), "FALSE"),
        (AND(), "AND"),
        (OR(), "OR"),
        (NOT(), "NOT"),
        (SUCC(), "SUCC"),
        (PLUS(), "PLUS"),
        (PLUS_2(), "PLUS_ALT"),
        (MULT(), "MULT"),
        (MULT_2(), "MULT_ALT"),
        (POW(), "POW"),
        (POW_2(), "POW_ALT1"),
        (POW_3(), "POW_ALT2"),
    ];

    if let Some((_, name)) = definitions.iter().find(|(def, _)| def == term) {
        return name.to_string();
    }

    match term {
        Debruijn::Index(idx) => idx.to_string(),
        Debruijn::Abstraction { body } => format!("(λ {})", to_string(body)),
        Debruijn::Application { func, arg } => format!("({} {})", to_string(func), to_string(arg)),
    }
}

#[cfg(test)]
mod test {
    use crate::{common_terms::*, debruijn::Debruijn};

    #[test]
    fn common_terms_parse_correctly() {
        assert_eq!(IDENT(), Debruijn::from(IDENT_STR()));
        assert_eq!(TRUE(), Debruijn::from(TRUE_STR()));
        assert_eq!(FALSE(), Debruijn::from(FALSE_STR()));
        assert_eq!(AND(), Debruijn::from(AND_STR()));
        assert_eq!(OR(), Debruijn::from(OR_STR()));
        assert_eq!(NOT(), Debruijn::from(NOT_STR()));
        assert_eq!(SUCC(), Debruijn::from(SUCC_STR()));
        assert_eq!(PLUS(), Debruijn::from(PLUS_STR()));
        assert_eq!(PLUS_2(), Debruijn::from(PLUS_2_STR()));
        assert_eq!(MULT(), Debruijn::from(MULT_STR()));
        assert_eq!(MULT_2(), Debruijn::from(MULT_2_STR()));
        assert_eq!(POW(), Debruijn::from(POW_STR()));
        assert_eq!(POW_2(), Debruijn::from(POW_2_STR()));
        assert_eq!(POW_3(), Debruijn::from(POW_3_STR()));
    }

    #[test]
    fn church_parses_correctly() {
        assert_eq!(CHURCH(0), Debruijn::from("λf.λx.x"));
        assert_eq!(CHURCH(1), Debruijn::from("λf.λx.f x"));
        assert_eq!(CHURCH(2), Debruijn::from("λf.λx.f (f x)"));
        assert_eq!(CHURCH(3), Debruijn::from("λf.λx.f (f (f x))"));
        assert_eq!(CHURCH(4), Debruijn::from("λf.λx.f (f (f (f x)))"));
        assert_eq!(CHURCH(5), Debruijn::from("λf.λx.f (f (f (f (f x))))"));

        assert_eq!(CHURCH(0), Debruijn::from(CHURCH_STR(0)));
        assert_eq!(CHURCH(1), Debruijn::from(CHURCH_STR(1)));
        assert_eq!(CHURCH(2), Debruijn::from(CHURCH_STR(2)));
        assert_eq!(CHURCH(3), Debruijn::from(CHURCH_STR(3)));
        assert_eq!(CHURCH(4), Debruijn::from(CHURCH_STR(4)));
        assert_eq!(CHURCH(5), Debruijn::from(CHURCH_STR(5)));
    }

    #[test]
    fn church_2() {
        assert_eq!(from_church(&CHURCH(0)), Some(0));
        assert_eq!(from_church(&CHURCH(1)), Some(1));
        assert_eq!(from_church(&CHURCH(2)), Some(2));
        assert_eq!(from_church(&CHURCH(3)), Some(3));
        assert_eq!(from_church(&CHURCH(4)), Some(4));
        assert_eq!(from_church(&CHURCH(5)), Some(5));
        assert_eq!(from_church(&IDENT()), None);
        assert_eq!(from_church(&TRUE()), None);
        assert_eq!(from_church(&FALSE()), None);
        assert_eq!(from_church(&AND()), None);
        assert_eq!(from_church(&OR()), None);
        assert_eq!(from_church(&NOT()), None);
        let almost_church = Debruijn::from("λf.λx.f (f (f (f (f f))))");
        assert_eq!(from_church(&almost_church), None)
    }
}
