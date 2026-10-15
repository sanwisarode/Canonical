use crate::search::*;
use crate::core::*;
use crate::memory::*;
use crate::stats::*;
use rayon::prelude::*;
use std::sync::atomic::{Ordering, AtomicUsize, AtomicBool};
use std::sync::Arc;
use std::collections::HashMap;
// use std::time::{Duration, Instant};
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
    decl: W<Decl>,
    _owned_linked: Vec<S<Linked>>
}

impl Frame {
    fn new(component: Component, parent: Option<W<Frame>>) -> Self {
        Frame { total_weight: 0.0, component, fuel: 0.0, extra_entropy: 0.0, parent, domain: Vec::new(), stats: SearchInfo::new_meta(), children: None }
    }

    fn contains(&self, meta: &W<Meta>) -> bool {
        self.component.next.meta == *meta || self.component.unassigned.contains(meta)
    }

    fn select(&mut self, meta: W<Meta>) {
        if self.component.next.meta == meta { return; }
        let i = self.component.unassigned.iter().position(|m| *m == meta).unwrap();
        self.component.unassigned[i] = self.component.next.meta.clone();
        self.component.next = MetaInfo::new(meta);
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
    /// Creates a new Prover for the specified `Decl`.
    pub fn new(decl: W<Decl>) -> Self {
        let gamma = decl.borrow().typ.as_ref().unwrap().borrow().gamma.clone();
        let entry = &gamma.linked.as_ref().unwrap().borrow().node.entry;
        let node = Node {
            entry: Entry { params_id: entry.params_id, lets_id: entry.lets_id, subst: None,
                context: Some(Type(decl.clone(), gamma.clone()))},
            bindings: gamma.linked.as_ref().unwrap().borrow().node.bindings.clone()
        };
        let mut owned_linked = Vec::new();
        let es = ES::new().append(node, &mut owned_linked);
        let ty = Type(decl.clone(), es);
        let meta = S::new(Meta::new(ty));

        let frame = S::new(Frame::new(Component {
            unassigned: Vec::new(), next: MetaInfo::new(meta.downgrade()), meta_entropy: 0.0,
        }, None));

        Prover {
            frames: vec![frame.downgrade()],
            frame, size: 0,
            meta, decl, _owned_linked: owned_linked
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

        let components = split(&unassigned);
        let sum: f64 = components.iter().map(|p| p.meta_entropy).sum();

        let mut children = Vec::new();
        for component in components {
            let entropy = extra_entropy + sum - component.meta_entropy;
            let mut child_frame = Frame::new(component, Some(frame.clone()));
            child_frame.populate(fuel, entropy);
            let child = S::new(child_frame);
            children.push(child);
        }
        return children;
    }

    /// Apply a user choice while keeping the frame tree consistent.
    pub fn refine(&mut self, meta: W<Meta>, head: DeBruijnIndex) -> bool {
        let Some(i) = self.frames.iter().position(|f| f.borrow().contains(&meta)) else { return false; };
        let mut frame = self.frames[i].clone();
        frame.borrow_mut().select(meta);
        frame.borrow_mut().populate(1e4, 0.0);
        let Some(j) = frame.borrow().domain.iter().position(|e| e.0.head.0.0 == head.0.0 && e.0.head.1 == head.1) else { return false; };
        let element = frame.borrow_mut().domain.remove(j);
        let children = self.assign(frame.clone(), element);
        self.frames.swap_remove(i);
        self.frames.extend(children.iter().map(|f| f.downgrade()));
        frame.borrow_mut().children = Some(children);
        self.size += 1;
        true
    }

    pub fn complete(&mut self, next_root: W<Meta>) -> bool {
        if next_root.borrow().assignment.is_some() { return true }

        let Some(idx) = self.frames.iter().position(|f| f.borrow().contains(&next_root)) else { return false };
        let orig = self.frames[idx].clone();
        orig.clone().borrow_mut().select(next_root.clone());
        orig.clone().borrow_mut().populate(1e4, 0.0);

        let component = Component { unassigned: Vec::new(), next: MetaInfo::new(next_root.clone()), meta_entropy: 0.0 };
        let frame = S::new(Frame::new(component, None));
        let w = frame.downgrade();
        let saved_frame = std::mem::replace(&mut self.frame, frame);
        let saved_frames = std::mem::replace(&mut self.frames, vec![w]);
        let saved_limit = LIMIT.load(Ordering::Acquire);
        LIMIT.store(10_000_000, Ordering::Release);

        let solved = AtomicBool::new(false);
        self.prove(&|_| {
            solved.store(true, Ordering::Relaxed);
            RUN.store(false, Ordering::Relaxed);
        }, false);

        LIMIT.store(saved_limit, Ordering::Release);
        self.frame = saved_frame;
        self.frames = saved_frames;
        let solved = solved.into_inner();

        if solved {
            let siblings = orig.borrow().component.unassigned.clone();
            let fuel = orig.borrow().fuel;
            let extra = orig.borrow().extra_entropy;
            let components = split(&siblings);
            let sum: f64 = components.iter().map(|p| p.meta_entropy).sum();
            let mut children = Vec::new();
            for component in components {
                let entropy = extra + sum - component.meta_entropy;
                let mut child = Frame::new(component, Some(orig.clone()));
                child.populate(fuel, entropy);
                children.push(S::new(child));
            }
            self.frames.swap_remove(idx);
            self.frames.extend(children.iter().map(|f| f.downgrade()));
            orig.clone().borrow_mut().children = Some(children);
            self.size += 1;
        }
        solved
    }

    /// Gets the current (partial) term of the prover.
    pub fn get_term(&self) -> Term {
        Term { base: self.meta.downgrade(), es: self.meta.borrow().gamma.clone() }
    }

    /// Start proof search, with a callback for solutions.
    pub fn prove<F>(&mut self, callback: &F, verbose: bool) -> (DFSResult, u32) where F: Fn(Term) + Send + Sync {
        reset();
        let mut depth = 1e4;
        let previous_steps = 0;
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
        }
        acc.steps = STEP_COUNT.load(Ordering::Relaxed);
        (acc, previous_steps)
    }

    fn backtrack(&mut self, mut parent: W<Frame>) {
        // Post-condition:
        // 1) All frames with frame.parent as an ancestor are unassigned and dropped
        // 2) frame.parent is unassigned and added back to self.frames
        let frame = parent.borrow_mut();
        if let Some(children) = &frame.children {
            for child in children {
                self.backtrack(child.downgrade());
                child.downgrade().borrow_mut().component.next.meta.borrow_mut().stats
                    .add_branch(&child.downgrade().borrow().stats);

                // By our post-condition, child will now be unassigned and added to
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

            let stats = frame.component.next.meta.borrow_mut().unassign();
            frame.stats.add_branch(&stats);
            frame.children = None;
            self.frames.push(parent);
            self.size -= 1;
        } else if !frame.domain.is_empty() {
            frame.component.next.meta.borrow_mut().stats.unknown = true;
        }
    }

    fn parallelize(&self, frame: &Frame) -> bool {
        // return false;
        return NUM_JOBS.load(Ordering::Relaxed) < 100 && frame.domain.len() > 2 &&
            frame.fuel/1000000.0 < frame.component.meta_entropy + frame.extra_entropy;
    }

    // Moving parallelism branch of dfs to new function
    fn parallelize_frame<F>(&mut self, mut frame: W<Frame>, max_size: usize, callback: &F) where F: Fn(Term) + Send + Sync {
        let mut provers = Vec::new();
        let mut maps = Vec::new();
        // let mut domain = Vec::new();
        // domain.append(&mut frame.domain); // ownership hack
        while let Some(element) = frame.clone().borrow_mut().domain.pop() {
            // no need to add components.
            // let components = frame.assign(self.frames.len() + 1, element);
            // self.components.extend(components);
            // self.frames.push(frame);
            let children = self.assign(frame.clone(), element);

            self.size += 1;
            let len = self.frames.len();
            self.frames.extend(children.iter().map(|x| x.downgrade()));
            frame.borrow_mut().children = Some(children);

            let (prover, map) = self.clone_with_map();
            provers.push(prover);
            maps.push(map);

            self.size -= 1;
            self.frames.truncate(len);
            frame.borrow_mut().children = None;

            // regain ownership
            // frame = self.frames.pop().unwrap();


            frame.borrow_mut().component.next.meta.borrow_mut().unassign();
            
            // self.components.truncate(frame.truncate);
        }

        let options = provers.len();
        NUM_JOBS.fetch_add(options, Ordering::Relaxed);

        provers.par_iter_mut().for_each(|prover| { prover.dfs(max_size, callback); });

        NUM_JOBS.fetch_sub(options, Ordering::Relaxed);

        let mut meta = frame.borrow().component.next.meta.clone();
        meta.borrow_mut().stats = SearchInfo::new_branch();
        frame.borrow_mut().stats = SearchInfo::new_branch();
        for (prover, map) in provers.iter().zip(&maps) {
            let worker = map[&meta].clone();
            meta.borrow_mut().stats.add_branch(&worker.borrow().stats);
            frame.borrow_mut().stats.add_branch(&prover.frame.borrow().stats);
        }
    }


    //Selecting component based on margin = fuel - (component.meta_entropy + extra_entropy)
    fn select_frame(&self) -> usize {
        for (i, frame) in self.frames.iter().enumerate() {
            if frame.borrow().component.next.has_rigid_equation { return i; }
        }

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

    fn dfs<F>(&mut self, max_size: usize, callback: &F) -> bool where F: Fn(Term) + Send + Sync {
        while RUN.load(Ordering::Relaxed) {
            if STEP_COUNT.fetch_add(1, Ordering::Relaxed) >= LIMIT.load(Ordering::Relaxed) {
                RUN.store(false, Ordering::Relaxed);
                break
            }
            // TODO statistics accumulation on finished assignment and finished metavariable (attempt?)
            if self.frames.is_empty() { callback(self.get_term()); return true }
            let mut frame = self.frames.swap_remove(self.select_frame());

            if self.size < max_size {
                // Root-only (basic): if frame.borrow().parent.is_none() && self.parallelize(frame.borrow()) {
                if self.parallelize(frame.borrow()) {
                    self.parallelize_frame(frame.clone(), max_size, callback);
                    self.backtrack(self.frame.downgrade());
                    return false
                } else if let Some(element) = frame.borrow_mut().domain.pop() {
                    let children = self.assign(frame.clone(), element);
                    if children.iter().any(|x| x.borrow().prune()) {
                        let stats = frame.borrow_mut().component.next.meta.borrow_mut().unassign();
                        frame.borrow_mut().stats.add_branch(&stats);
                        frame.borrow_mut().component.next.meta.borrow_mut().stats.unknown = true;
                        self.frames.push(frame);
                    } else {
                        self.size += 1;
                        self.frames.extend(children.iter().map(|x| x.downgrade()));
                        frame.borrow_mut().children = Some(children);
                    }
                    continue;
                }
            } else {
                frame.borrow_mut().component.next.meta.borrow_mut().stats.unknown = true;
            }

            if let Some(parent) = frame.borrow().parent.clone() {
                frame.borrow().component.next.log(frame.borrow().component.meta_entropy);
                self.backtrack(parent);
            } else {
                self.frames.push(frame); // last iteration adds the frame back.
                return false
            }
        }
        self.backtrack(self.frame.downgrade());
        false
    }
}

unsafe impl Send for Prover {}
unsafe impl Sync for Prover {}


impl Prover {
    fn replay(&mut self, mut new_frame: W<Frame>, orig_frame: W<Frame>, map: &mut HashMap<W<Meta>, W<Meta>>) {
        new_frame.borrow_mut().select(map[&orig_frame.borrow().component.next.meta].clone());
  
        new_frame.borrow_mut().stats = SearchInfo::new_branch();
        new_frame.borrow_mut().populate(orig_frame.borrow().fuel, orig_frame.borrow().extra_entropy);

        // An unassigned frame (children == None) is a frontier leaf: nothing to
        // replay. Its fresh domain was computed above.
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
        for (old, new) in orig_frame.borrow().component.next.meta.borrow().assignment.as_ref().unwrap().args.iter().zip(&element.0.args) {
            map.insert(old.downgrade(), new.downgrade());
        }

        // Replay the assignment: creates the fresh child frames (with fresh child
        // metas as the assignment's args) and wires their parent pointers to new_frame
        let children = self.assign(new_frame.clone(), element);
        new_frame.borrow_mut().children = Some(children);
        
        self.size += 1;

        // Match child components by metavariable; user selections can change their order.
        let n = orig_frame.borrow().children.as_ref().unwrap().len();
        for i in 0..n {
            let orig_child = orig_frame.borrow().children.as_ref().unwrap()[i].downgrade();
            let selected = &map[&orig_child.borrow().component.next.meta];
            let new_child = new_frame.borrow().children.as_ref().unwrap().iter()
                .find(|f| f.borrow().contains(selected)).unwrap().downgrade();
            self.replay(new_child, orig_child, map);
        }
    }
}

impl Prover {
    fn clone_with_map(&self) -> (Self, HashMap<W<Meta>, W<Meta>>) {
        let mut prover = Self::new(self.decl.clone());
        prover.frames.clear();
        let mut map = HashMap::from([(self.meta.downgrade(), prover.meta.downgrade())]);
        prover.replay(prover.frame.downgrade(), self.frame.downgrade(), &mut map);
        (prover, map)
    }
}

impl Clone for Prover {
    fn clone(&self) -> Self {
        let mut prover = Self::new(self.decl.clone());
        prover.frames.clear();
        let mut map = HashMap::from([(self.meta.downgrade(), prover.meta.downgrade())]);

        // Rebuild the tree onto fresh memory.
        prover.replay(prover.frame.downgrade(), self.frame.downgrade(), &mut map);

        prover
    }
}
