use crate::search::*;
use crate::core::*;
use crate::memory::*;
use crate::stats::*;
use crate::compiler::compile;
use rayon::prelude::*;
use std::sync::atomic::{Ordering, AtomicUsize, AtomicBool};
use std::sync::Arc;
use rustc_hash::FxHashMap as HashMap;
use crate::independence::split;

/// The number of Rayon jobs yet to be completed.
pub static NUM_JOBS: AtomicUsize = AtomicUsize::new(0);

struct Frame {
    domain: Vec<(Assignment, Vec<Box<dyn Constraint>>, AssignmentInfo)>,
    total_weight: f64,
    stats: SearchInfo,
    truncate: usize,
    component: Component,
}

struct Component {
    beginning: Vec<W<Meta>>,
    next: MetaInfo,
    end: Vec<W<Meta>>,
    fuel: f64,
    meta_entropy: f64,
    extra_entropy: f64,
    parent: usize
}

pub struct Prover {
    pub meta: S<Meta>,
    frames: Vec<Frame>,
    components: Vec<Component>,

    tb_ref: W<TypeBase>,
    problem_bind: W<Bind>,
    _owned_linked: Vec<S<Linked>>
}

impl Frame {
    fn new(component: Component, truncate: usize) -> Self {
        let mut domain = Vec::new();
        let mut total_weight = 0.0;
        for (db, linked) in component.next.meta.borrow().gamma.iter_unify(
            component.next.meta.borrow().typ.as_ref().unwrap().0.clone()) {
            let attempt = test(db, linked, component.next.meta.clone());
            if let Some(Some(result)) = attempt {
                total_weight += result.2.weight();
                domain.push(result);
            }
        }
        Frame { total_weight, component, domain, stats: SearchInfo::new_branch(), truncate }
    }

    fn assign(&mut self, index: usize, element: (Assignment, Vec<Box<dyn Constraint>>, AssignmentInfo)) -> Vec<Component> {
        let (assn, constraints, info) = element;
        let args: Vec<W<Meta>> = assn.args.iter().map(|x| x.downgrade()).collect();
        let unassigned = [self.component.beginning.as_slice(), &args, &self.component.end].concat();
        let components = split(unassigned);
        let sum: f64 = components.iter().map(|(_, entropy)| entropy).sum();
        self.component.next.meta.borrow_mut().assign(assn, constraints);
        components.into_iter().map(|component|
            Component::new(self, component, sum, index, info.weight())
        ).collect()
    }
}

impl Component {
    fn new(frame: &Frame, component: (Vec<W<Meta>>, f64), sum: f64, parent: usize, weight: f64) -> Self {
        let mut next = Meta::next_new(&component.0);
        next.next.meta.borrow_mut().had_rigid_equation = next.next.has_rigid_equation;
        let (beginning, end) = component.0.split_at(next.index);
        Component {
            fuel: frame.component.fuel * (weight / frame.total_weight),
            meta_entropy: component.1,
            extra_entropy: frame.component.extra_entropy + sum - component.1,
            next: next.next,
            beginning: beginning.to_vec(),
            end: end[1..].to_vec(),
            parent
        }   
    }

    fn prune(&self) -> bool {
        return self.fuel < self.meta_entropy + self.extra_entropy;
    }
}


impl Prover {
    /// Creates a new Prover for the specified `Type`. 
    pub fn new(tb_ref: W<TypeBase>, problem_bind: W<Bind>) -> Self {
        let entry = &tb_ref.borrow().codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.entry;
        let node = Node { 
            entry: Entry { params_id: entry.params_id, lets_id: entry.lets_id, subst: None, 
                context: Some(Type(tb_ref.clone(), tb_ref.borrow().codomain.borrow().gamma.clone(), problem_bind.clone()))}, 
            bindings: tb_ref.borrow().codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.bindings.clone() 
        };
        let mut owned_linked = Vec::new();
        let es = ES::new().append(node, &mut owned_linked);
        compile(Type(tb_ref.clone(), ES::new(), problem_bind.clone()));
        let ty = Type(tb_ref.clone(), es, problem_bind.clone());
        let meta = S::new(Meta::new(ty));
        Prover { 
            frames: Vec::new(), 
            components: vec![Component { beginning: Vec::new(), next: MetaInfo::new(meta.downgrade()), end: Vec::new(), fuel: 0.0, meta_entropy: 0.0, extra_entropy: 0.0, parent: 0 }], 
            meta, tb_ref, problem_bind, _owned_linked: owned_linked 
        }
    }

    /// Gets the current (partial) term of the prover. 
    pub fn get_term(&self) -> Term {
        Term { base: self.meta.downgrade(), es: self.meta.borrow().gamma.clone() }
    }

    /// Start proof search, with a callback for solutions.
    pub fn prove<F>(&mut self, callback: &F, verbose: bool, run: &AtomicBool) -> (DFSResult, u32) where F: Fn(Term) + Send + Sync {
        reset();
        let mut depth = 1e4;
        let mut previous_steps = 0;
        let mut acc = DFSResult { unknown_count: 0, steps: 0, entropy: 1.0, solution_count: 0, attempts: 0, branching: 0 };
        // Iterative deepening. 
        while run.load(Ordering::Relaxed) {
            let max_size = ((depth as f32).ln_1p()*4.0) as usize;
            if verbose { println!("entropy (log): {}", (depth as f32).ln_1p()); }
            self.components[0].fuel = depth;
            let success = self.dfs(max_size, run);
            if success {
                callback(self.get_term());
            }
            // if verbose { println!("ratio: {}", result.steps as f32 / previous_steps as f32); }
            
            // previous_steps = result.steps;
            depth *= 3.0;

            // Update the global statistics maps.
            META_MAP.store(Arc::new(META_CONTROL.probe_tls()));
            ASSIGNMENT_MAP.store(Arc::new(ASSIGNMENT_CONTROL.probe_tls()));
            
            // If all branches were fully explored, we can terminate.
            // let fail = result.unknown_count == 0;
            // acc.add(result);
            // if fail { 
            //     RUN.store(false, Ordering::Relaxed);
            //     return (acc, previous_steps)
            // }
        }
        acc.steps = STEP_COUNT.load(Ordering::Relaxed);
        (acc, previous_steps)
    }

    fn backtrack(&mut self, index: usize) {
        while self.frames.len() > index {
            let mut frame = self.frames.pop().unwrap();
            frame.stats.add_branch(&frame.component.next.meta.borrow_mut().unassign());
            frame.component.next.meta.borrow_mut().stats.add_branch(&frame.stats);
            frame.component.next.log(&DFSResult { unknown_count: 1, solution_count: 0, steps: 0, entropy: 0.0, branching: 0, attempts: 0 }, 1.0, &frame.stats); // TODO dummy values

            self.components.truncate(frame.truncate);
            self.components.push(frame.component);
        }
    }

    fn step(&mut self, mut index: usize) -> bool {
        'outer: loop {
            self.backtrack(index);
            let Some(frame) = self.frames.get_mut(index - 1) else { return false; };
            if let Some(element) = frame.domain.pop() {
                let assn_stats = frame.component.next.meta.borrow_mut().unassign(); // TODO two unassignment points, bad. Also one extra unassignment.
                frame.stats.add_branch(&assn_stats); 
                self.components.truncate(frame.truncate);

                let mut components = frame.assign(index, element);

                if !components.iter().any(Component::prune) {
                    index = frame.component.parent;
                    continue 'outer;
                }

                self.components.append(&mut components);

                return true;
            }
            index = frame.component.parent;
        }
    }

    fn parallelize(&self, frame: &Frame) -> bool {
        return false;
    }

    fn dfs(&mut self, max_size: usize, run: &AtomicBool) -> bool {
        while run.load(Ordering::Relaxed) {
            STEP_COUNT.fetch_add(1, Ordering::Relaxed);
            let Some(component) = self.components.pop() else { return true };
            if self.frames.len() < max_size { 
                let mut frame = Frame::new(component, self.components.len());
                if self.parallelize(&frame) {
                    let mut provers = Vec::new();
                    let mut domain = Vec::new();
                    domain.append(&mut frame.domain); // ownership hack
                    while let Some(element) = domain.pop() {
                        // no need to add components.
                        let _components = frame.assign(self.frames.len() + 1, element);
                        
                        self.frames.push(frame);

                        provers.push(self.clone());
                        
                        // regain ownership
                        frame = self.frames.pop().unwrap();
                    }

                    let child_run = AtomicBool::new(true);

                    let result = provers.into_par_iter().any(|mut prover| prover.dfs(max_size, &child_run));
                    // perform the successful assignment. Why don't we use callbacks, again?
                    // also, we need to obtain the SearchInfo. Maybe dfs needs to return SearchInfo.

                    child_run.store(false, Ordering::Relaxed);

                } else {
                    self.frames.push(frame); 
                }
            }
            if !self.step(self.frames.len()) { return false; }
        }
        return false;
    }
}

unsafe impl Send for Prover {}
unsafe impl Sync for Prover {}

impl Clone for Prover {
    // The cloned prover will not backtrack into the work of the parent prover.
    fn clone(&self) -> Self {
        let mut prover = Prover::new(self.tb_ref.clone(), self.problem_bind.clone());
        for (index, frame) in self.frames.iter().enumerate() {
            // we assume that we always work on the last component.
            let component = prover.components.pop().unwrap();
            let mvar = frame.component.next.meta.clone();
            let mvar_new = component.next.meta.clone();
            let mut new_frame = Frame {
                domain: Vec::new(),
                total_weight: frame.total_weight,
                stats: SearchInfo::new_branch(),
                truncate: frame.truncate,
                component
            };
            let db = mvar.borrow().assignment.as_ref().unwrap().head.clone();
            let linked = mvar_new.borrow().gamma.sub_es(db.0).linked.unwrap();
            let element = test(db, linked, mvar_new.clone()).unwrap().unwrap();

            // we assume that next_new is deterministic.
            let mut components = new_frame.assign(index, element);
            prover.components.append(&mut components);
            
            prover.frames.push(new_frame);
        }
        prover
    }
}