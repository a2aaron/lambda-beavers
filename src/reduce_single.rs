use std::rc::Rc;

use crate::{debruijn::Debruijn, graph::get_redexes, reduce::ReductionResult, replace::VisitOrder};

pub struct Reducer {
    pub root: Rc<Debruijn>,
    visit_order: VisitOrder,
}

impl Reducer {
    pub fn new(root: Debruijn, visit_order: VisitOrder) -> Self {
        Self {
            root: Rc::new(root),
            visit_order,
        }
    }

    pub fn reduce_one(&mut self) -> Option<ReductionResult> {
        if let Some(redex) = get_redexes(self.root.clone(), self.visit_order).next() {
            self.root = redex.beta_reduce(&self.root);
            None
        } else {
            let bnf = (*self.root).clone();
            Some(ReductionResult::NormalForm(bnf))
        }
    }
}
