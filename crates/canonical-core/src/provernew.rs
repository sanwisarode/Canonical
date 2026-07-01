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
    tree_entropy: f64,
    component: Component
}

struct Component {
    beginning: Vec<W<Meta>>,
    next: W<Meta>,
    end: Vec<W<Meta>>,
    tree_entropy: f64,
    meta_entropy: f64,
    extra_entropy: f64,
    parent: usize
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

impl Frame {
    fn new(component: Component) -> Self {
        let domain = Meta::domain(component.next.clone());
        Frame { tree_entropy: component.tree_entropy * domain.len() as f64, component, domain }
    }
}

impl Component {
    fn new(frame: &Frame, component: (Vec<W<Meta>>, f64), sum: f64, parent: usize) -> Self {
        let next = Meta::next_new(&component.0);
        let (beginning, end) = component.0.split_at(next.index);
        Component {
            tree_entropy: frame.tree_entropy,
            meta_entropy: component.1,
            extra_entropy: frame.component.extra_entropy + sum - component.1,
            next: next.next.meta,
            beginning: beginning.to_vec(),
            end: end[1..].to_vec(),
            parent
        }   
    }
}


impl Prover {
    fn backtrack(&mut self, index: usize) {
        while self.frames.len() > index {
            self.frames.pop().unwrap().component.next.borrow_mut().unassign();
        }
    }

    fn step(&mut self, mut index: usize) -> bool {
        loop {
            self.backtrack(index);
            if index == 0 { return false; }
            let frame = &mut self.frames[index-1];
            if let Some((assn, constraints, _)) = frame.domain.pop() {
                let args: Vec<W<Meta>> = frame.component.next.borrow().assignment.as_ref().unwrap().args.iter().map(|x| x.downgrade()).collect();
                let unassigned = [frame.component.beginning.as_slice(), &args, &frame.component.end].concat();
                let components = split(unassigned);
                let sum: f64 = components.iter().map(|(_, entropy)| entropy).sum();
                frame.component.next.borrow_mut().assign(assn, constraints);
                for component in components {
                    self.components.push(Component::new(frame, component, sum, index));
                }
                return true;
            }
            index = frame.component.parent;
        }
    }

    fn dfs(&mut self) -> bool {
        while RUN.load(Ordering::Relaxed) {
            let Some(component) = self.components.pop() else { return true };
            self.frames.push(Frame::new(component));
            if !self.step(self.frames.len()) { return false; }
        }
        return false;
    }
}