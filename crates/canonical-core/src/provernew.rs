use crate::search::*;
use crate::core::*;
use crate::memory::*;
use crate::stats::*;
use crate::compiler::compile;
use rayon::prelude::*;
use std::sync::atomic::{Ordering, AtomicUsize};
use std::sync::Arc;
use rustc_hash::FxHashMap as HashMap;
use crate::independence::split;

/// The number of Rayon jobs yet to be completed.
pub static NUM_JOBS: AtomicUsize = AtomicUsize::new(0);

struct Frame {
    domain: Vec<(Assignment, Vec<Box<dyn Constraint>>, AssignmentInfo)>,
    component: Component
}

struct Component {
    beginning: Vec<W<Meta>>,
    next: W<Meta>,
    end: Vec<W<Meta>>,
    next_index: usize,
    entropy: f64,
    parent: Option<usize>
}

pub struct Prover {
    pub meta: S<Meta>,
    frames: Vec<Frame>,
    components: Vec<Component>
}

impl Meta {
    fn domain(next: W<Meta>) -> Vec<(Assignment, Vec<Box<dyn Constraint>>, AssignmentInfo)> {
        let mut options = Vec::new();
        for (db, linked) in next.borrow().gamma.iter_unify(next.borrow().typ.as_ref().unwrap().0.clone()) {
            let attempt = test(db, linked, next.clone());
            if let Some(Some(result)) = attempt {
                options.push(result);
            }
        }
        return options;
    }
}


impl Prover {
    fn backtrack(&mut self, index: usize) {
        while self.frames.len() > index {
            let mut frame = self.frames.pop().unwrap();
            frame.component.next.borrow_mut().unassign();
        }
    }

    fn increment(&mut self, mut parent: Option<usize>) -> bool {
        while let Some(index) = parent {
            self.backtrack(index);
            let frame = &mut self.frames[index];
            if let Some((assn, constraints, _)) = frame.domain.pop() {
                frame.component.next.borrow_mut().assign(assn, constraints);
                return true;
            }
            parent = frame.component.parent;
        }
        return false;
    }

    fn dfs(&mut self) -> bool {
        while RUN.load(Ordering::Relaxed) {
            let Some(component) = self.components.pop() else { return true };
            self.frames.push(Frame { domain: Meta::domain(component.next.clone()), component });
            if !self.increment(Some(self.frames.len())) { return false; }

            // register the new components.
        }
        return false;
    }
}