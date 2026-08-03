use crate::core::*;
use crate::heuristic::*;
use crate::memory::{S, W, WVec};
use crate::stats::*;
use std::sync::atomic::AtomicBool;

/// Set `RUN` to false to cancel terminate the ongoing problem.
pub static RUN: AtomicBool = AtomicBool::new(true);

/// Generic flag for A/B testing: gate the experimental behavior on this, and the
/// harness in canonical-compat will run with it off (A) and on (B).
pub static EXPERIMENT: AtomicBool = AtomicBool::new(false);

/// Results from a DFS subtree. 
#[derive(Clone)]
pub struct DFSResult {
    pub unknown_count: u32,
    pub solution_count: u32,
    pub steps: u32,
    pub entropy: f64,
    pub branching: usize,
    pub attempts: u32
}

impl DFSResult {
    /// Add `other` into `self`.
    pub fn add(&mut self, other: Self) {
        self.unknown_count += other.unknown_count;
        self.steps += other.steps;
        self.solution_count += other.solution_count;
        self.branching += other.branching;
        self.attempts += other.attempts;
    }
}

/// Construct and test the `Assignment` from refining `meta` with `head`.
pub fn test(head: DeBruijnIndex, curr: W<Linked>, mut meta: W<Meta>) -> Option<Option<(Assignment, Vec<Box<dyn Constraint>>, AssignmentInfo)>> {
    let Some(context) = curr.borrow().node.entry.context.as_ref() else { return None };
    let Some(tb) = context.0.borrow().types.borrow()[head.1].as_ref() else { return None };
    let args: Vec<S<Meta>> = tb.borrow().args_metas(Some(meta.clone()));
    let gamma = meta.borrow().gamma.clone();
    let mut _owned_linked = Vec::new();
    let var_type = context.get(head.1, Entry::subst(Subst(WVec::new(&args), gamma.clone())), &mut _owned_linked);

    meta.borrow_mut().assignment = Some(Assignment {
        head, args, bind: var_type.2.clone(), changes: Vec::new(), _owned_linked,
        has_rigid_type: matches!(var_type.codomain().whnf::<true, ()>(&mut Vec::new(), &mut ()).1, Head::Var(_)),
        var_type: Some(var_type.clone()),
    });

    let Some(constraints) = meta.clone().borrow_mut().test_assignment(meta.clone()) else {
        // Constraint violation.
        meta.borrow_mut().assignment = None;
        return Some(None);
    };
    
    let assignment_info = AssignmentInfo::new(meta.clone());
    let mut assignment = meta.borrow_mut().assignment.take().unwrap();

    // Calculate the `typ` and `gamma` of the new metavariables.
    for i in 0..tb.borrow().types.borrow().params.len() {
        let arg = assignment.args[i].borrow_mut(); 
        let var_id = next_u64();
        let let_id = next_u64();
        let typ = var_type.get(Index::Param(i), 
            Entry { params_id: var_id, lets_id: let_id, subst: None, context: None }, &mut assignment._owned_linked
        );
        arg.gamma = gamma.append(Node { 
            entry: Entry { params_id: var_id, lets_id: let_id, subst: None, context: Some(typ.clone()) }, 
            bindings: arg.bindings.clone() 
        }, &mut assignment._owned_linked);
        arg.typ = Some(typ);
    }
    Some(Some((assignment, constraints, assignment_info)))
}