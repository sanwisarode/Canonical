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

struct Component {
    mvars: Vec<W<Meta>>,
    entropy: f64,
    parent: Option<usize>,
    next: W<Meta>,
    domain: Vec<(Assignment, Vec<Box<dyn Constraint>>, AssignmentInfo)>
}

pub struct Prover {
    pub meta: S<Meta>,
    frames: Vec<Component>,
    components: Vec<Component>
}


impl Prover {
    fn backtrack(&mut self, index: usize) {
        while self.frames.len() > index + 1 {
            let mut frame = self.frames.pop().unwrap();
            frame.next.borrow_mut().unassign();
        }
    }

    fn increment(&mut self, mut parent: Option<usize>) -> bool {
        while let Some(index) = parent {
            self.backtrack(index);
            let frame = &mut self.frames[index];
            if let Some((assn, constraints, _)) = frame.domain.pop() {
                frame.next.borrow_mut().assign(assn, constraints);
                return true;
            }
            parent = frame.parent;
        }
        return false;
    }

    fn dfs(&mut self) -> bool {
        while RUN.load(Ordering::Relaxed) {
            let Some(component) = self.components.pop() else { return true };
            self.frames.push(component);
            if !self.increment(Some(self.frames.len() - 1)) { return false; }

            // register the new components.
        }
        return false;
    }
}