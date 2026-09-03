use crate::search::*;
use crate::core::*;
use crate::memory::*;
use crate::stats::*;
use crate::compiler::compile;
use rayon::prelude::*;
use std::sync::atomic::{Ordering, AtomicUsize, AtomicBool};
use std::sync::Arc;
use crate::independence::{split, Component};

/// The number of Rayon jobs yet to be completed.
pub static NUM_JOBS: AtomicUsize = AtomicUsize::new(0);

struct Frame {
    domain: Vec<(Assignment, Vec<Box<dyn Constraint>>, AssignmentInfo)>,
    total_weight: f64,
    stats: SearchInfo,
    component: Component,
    fuel: f64,
    extra_entropy: f64,
    parent: Option<W<Frame>>,
    
    /// The owned children frames. This is `None` if the current frame is
    /// unassigned.
    children: Option<Vec<S<Frame>>>
}

pub struct Prover {
    pub meta: S<Meta>,
    pub frame: S<Frame>,
    size: usize,
    frames: Vec<W<Frame>>,
    tb_ref: W<TypeBase>,
    problem_bind: W<Bind>,
    _owned_linked: Vec<S<Linked>>
}

impl Frame {
    fn new(component: Component, parent: Option<W<Frame>>) -> Self {
        Frame { total_weight: 0.0, component, fuel: 0.0, extra_entropy: 0.0, parent, domain: Vec::new(), stats: SearchInfo::new_branch(), children: None }
    }

    fn populate(&mut self, fuel: f64, extra_entropy: f64) {
        self.component.next.meta.borrow_mut().had_rigid_equation = self.component.next.has_rigid_equation;
        let mut domain = Vec::new();
        let mut total_weight = 0.0;
        for (db, linked) in self.component.next.meta.borrow().gamma.iter_unify(
            self.component.next.meta.borrow().typ.as_ref().unwrap().0.clone()) {
            let attempt = test(db, linked, self.component.next.meta.clone());
            if let Some(Some(result)) = attempt {
                total_weight += result.2.weight();
                domain.push(result);
            }
        }
        domain.reverse();
        self.total_weight = total_weight;
        self.fuel = fuel;
        self.extra_entropy = extra_entropy;
        self.domain = domain;
    }

    fn prune(&self) -> bool {
        return self.fuel < self.component.meta_entropy + self.extra_entropy;
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

        let frame = S::new(Frame::new(Component {
            unassigned: Vec::new(), next: MetaInfo::new(meta.downgrade()), meta_entropy: 0.0,
        }, None));

        Prover {
            frames: vec![frame.downgrade()],
            frame, size: 0,
            meta, tb_ref, problem_bind, _owned_linked: owned_linked
        }
    }

    fn assign(&mut self, mut frame: W<Frame>, element: (Assignment, Vec<Box<dyn Constraint>>, AssignmentInfo)) -> Vec<S<Frame>> {
        let (assn, constraints, info) = element;
        let args: Vec<W<Meta>> = assn.args.iter().map(|x| x.downgrade()).collect();
        let mut unassigned = frame.borrow().component.unassigned.clone();
        unassigned.extend(args);
        let fuel =  frame.borrow().fuel * (info.weight() / frame.borrow().total_weight);
        let extra_entropy =  frame.borrow().extra_entropy;
        frame.borrow_mut().component.next.meta.borrow_mut().assign(assn, constraints);

        let components = split(unassigned);
        let sum: f64 = components.iter().map(|p| p.meta_entropy).sum();

        let mut children = Vec::new();
        for component in components {
            let entropy = extra_entropy + sum - component.meta_entropy;
            let mut child_frame = Frame::new(component,
                Some(frame.clone()),
            );
            child_frame.populate(fuel, entropy);
            let child = S::new(child_frame);
            children.push(child);
        }
        return children;
    }

    /// Gets the current (partial) term of the prover.
    pub fn get_term(&self) -> Term {
        Term { base: self.meta.downgrade(), es: self.meta.borrow().gamma.clone() }
    }

    /// Start proof search, with a callback for solutions.
    pub fn prove<F>(&mut self, callback: &F, verbose: bool) -> (DFSResult, u32) where F: Fn(Term) + Send + Sync {
        reset();
        let mut depth = 1e4;
        let mut previous_steps = 0;
        let mut acc = DFSResult { unknown_count: 0, steps: 0, entropy: 1.0, solution_count: 0, attempts: 0, branching: 0 };
        // Iterative deepening. 
        while RUN.load(Ordering::Relaxed) {
            let max_size = ((depth as f32).ln_1p()*4.0) as usize;
            if verbose { println!("entropy (log): {}", (depth as f32).ln_1p()); }
            // self.frame.borrow_mut().fuel = depth;
            self.frame.borrow_mut().populate(depth, 0.0);
            self.dfs(max_size, callback);

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

    fn backtrack(&mut self, mut parent: W<Frame>) {
        // Invariant:
        // 1) All frames with frame.parent as an ancestor are unassigned and dropped
        // 2) frame.parent is unassigned and added back to self.frames
        // 3) parent accumulates all SearchInfo's from descendants
        let frame = parent.borrow_mut();
        if let Some(children) = &frame.children {
            for child in children {
                self.backtrack(child.downgrade());
                child.borrow()
                    .component
                    .next
                    .log(child.borrow().component.meta_entropy);

                // By our invariant, child will now be unassigned and added to
                // self.frames, so we should remove it from self.frames. We
                // could do away with this (except for the leaf nodes) by making
                // a backtrack_helper function that strictly does unassigning
                // and only add back to self.frames in the main backtrack
                // function. However, one main assumption is that self.frames is
                // usually very small, so this isn't too pressing.
                if let Some(i) = self.frames.iter().position(|f| f.points_to(child)) {
                    self.frames.swap_remove(i);
                }
            }

            frame.component.next.meta.borrow_mut().unassign();
            frame.children = None;
            self.frames.push(parent);
            self.size -= 1;
        } else {
            // In the case that parent.children is none, parent is unassigned.
            // Then, by our invariant, parent will already be contained in
            // self.frames, so no need to add it here.
            if !frame.domain.is_empty() {
                frame.component.next.meta.borrow_mut().stats.unknown = true;
            }
        }
    }

    fn parallelize(&self, frame: &Frame) -> bool {
        // return false;
        return NUM_JOBS.load(Ordering::Relaxed) < 100 && frame.domain.len() > 2 &&
            frame.fuel/1000000.0 < frame.component.meta_entropy + frame.extra_entropy;
    }

    // Moving parallelism branch of dfs to new function
    // fn parallelize_frame<F>(&mut self, mut frame: Frame, max_size: usize, callback: &F) -> Frame where F: Fn(Term) + Send + Sync {
    //     let mut provers = Vec::new();
    //     let mut domain = Vec::new();
    //     domain.append(&mut frame.domain); // ownership hack
    //     while let Some(element) = domain.pop() {
    //         // no need to add components.
    //         let components = frame.assign(self.frames.len() + 1, element);
    //         self.components.extend(components);
    //         self.frames.push(frame);
            
    //         provers.push(self.clone());

    //         // regain ownership
    //         frame = self.frames.pop().unwrap();
    //         frame.component.partition.next.meta.borrow_mut().unassign();
    //         self.components.truncate(frame.truncate);
    //     }

    //     let options = provers.len();
    //     NUM_JOBS.fetch_add(options, Ordering::Relaxed);

    //     let acc = provers.into_par_iter().map(|mut prover| {
    //         let mut result = SearchInfo::new_branch();
    //         result.add_branch(&prover.dfs(max_size, callback));
    //         result
    //     }).reduce(SearchInfo::new_branch, |mut a, b| {
    //         a.add_branch(&b);
    //         a
    //     });

    //     NUM_JOBS.fetch_sub(options, Ordering::Relaxed);

    //     frame.stats.add_branch(&acc);
    //     frame
    // }


    //Selecting component based on margin = fuel - (component.meta_entropy + extra_entropy)
    fn select_frame(&self) -> usize {
        let mut best = 0;
        let mut best_margin = f64::INFINITY;
        for (i, frame) in self.frames.iter().enumerate() {
            let frame = frame.borrow();
            let margin = frame.fuel - (frame.component.meta_entropy + frame.extra_entropy);
            if margin < best_margin {
                best_margin = margin;
                best = i;
            }
        }
        best
    }

    fn dfs<F>(&mut self, max_size: usize, callback: &F) where F: Fn(Term) + Send + Sync {
        while RUN.load(Ordering::Relaxed) {
            STEP_COUNT.fetch_add(1, Ordering::Relaxed);
            // TODO statistics accumulation on finished assignment and finished metavariable (attempt?)
            if self.frames.is_empty() { callback(self.get_term()); return }
            let mut frame = self.frames.swap_remove(self.select_frame());

            if self.size < max_size {
                if let Some(element) = frame.borrow_mut().domain.pop() {
                    let children = self.assign(frame.clone(), element);
                    self.size += 1;
                    if children.iter().all(|x| !x.borrow().prune()) {
                        self.frames.extend(children.iter().map(|x| x.downgrade()));
                        frame.borrow_mut().children = Some(children);
                        continue;
                    }
                    frame.borrow_mut().children = Some(children);
                }
            }

            if let Some(parent) = frame.borrow().parent.clone() {
                self.backtrack(parent);
            } else {
                self.frames.push(frame);
                return
            }
        }
        self.backtrack(self.frame.downgrade());
    }
}

unsafe impl Send for Prover {}
unsafe impl Sync for Prover {}


impl Prover {
    fn replay(&mut self, mut new_frame: W<Frame>, orig_frame: W<Frame>) {
  
        new_frame.borrow_mut().stats = orig_frame.borrow().stats.clone();
        new_frame.borrow_mut().fuel = orig_frame.borrow().fuel;
        new_frame.borrow_mut().extra_entropy = orig_frame.borrow().extra_entropy;

        // An unassigned frame (children == None) is a frontier leaf: nothing to
        // replay. Its fresh domain was already computed by Frame::new.
        if orig_frame.borrow().children.is_none() {
            self.frames.push(new_frame);
            return
        }

        // Reconstruct the element this frame assigned, on the fresh metavariable.
        let db: DeBruijnIndex = orig_frame.borrow().component.next.meta
            .borrow().assignment.as_ref().unwrap().head.clone();
        let meta = new_frame.borrow().component.next.meta.clone();
        let linked = meta.borrow().gamma.sub_es(db.0).linked.unwrap();
        let element = test(db, linked, meta.clone()).unwrap().unwrap();

        // Replay the assignment: creates the fresh child frames (with fresh child
        // metas as the assignment's args) and wires their parent pointers to new_frame
        let children = self.assign(new_frame.clone(), element);
        self.frames.extend(children.iter().map(|x| x.downgrade()));
        new_frame.borrow_mut().children = Some(children);
        
        self.size += 1;

        // Recurse into each child, matching original --> clone by index.
        let n = orig_frame.borrow().children.as_ref().unwrap().len();
        for i in 0..n {
            let new_child = new_frame.borrow().children.as_ref().unwrap()[i].downgrade();
            let orig_child = orig_frame.borrow().children.as_ref().unwrap()[i].downgrade();
            self.replay(new_child, orig_child);
        }
    }
}

impl Clone for Prover {
 
    fn clone(&self) -> Self {
        let meta = S::new(Meta::new(self.meta.borrow().typ.as_ref().unwrap().clone()));

        // Fresh, unassigned root frame mirroring the original's root component.
        let mut frame = S::new(Frame::new(
            Component {
                unassigned: Vec::new(),
                next: MetaInfo::new(meta.downgrade()),
                meta_entropy: 0.0,
            }, None
        ));
        frame.borrow_mut().populate(self.frame.borrow().fuel, self.frame.borrow().extra_entropy);

        // TODO: Set the parents of the children frames to None so the parallel
        // runs can't backtrack behind this (replaces the floor behavior).
        let mut prover = Prover {
            frames: Vec::new(),
            size: 0,
            frame,
            meta,
            tb_ref: self.tb_ref.clone(),
            problem_bind: self.problem_bind.clone(),
            _owned_linked: Vec::new(),
        };

        // Rebuild the tree onto fresh memory.
        prover.replay(prover.frame.downgrade(), self.frame.downgrade());

        prover
    }
}
