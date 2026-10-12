use Index::*;
use crate::memory::{S, W, WVec};
use std::sync::atomic::{AtomicU64, Ordering};
use std::iter;
use crate::stats::SearchInfo;
use std::cell::RefCell;
use std::ops::ControlFlow;
use core::slice::Iter;
use std::hash::{Hash, Hasher};

#[cfg(all(feature = "mimalloc", feature = "host-mimalloc"))]
compile_error!("features `mimalloc` and `host-mimalloc` are mutually exclusive: \
    a bundled mimalloc would shadow the host's `mi_*` symbols in the Lean cdylib");

#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// mimalloc provided by the host process (Lean's runtime), bound at load time.
/// Mirrors the `GlobalAlloc` impl of the `mimalloc` crate.
#[cfg(feature = "host-mimalloc")]
mod host_mimalloc {
    use std::alloc::{GlobalAlloc, Layout};
    use std::ffi::c_void;

    extern "C" {
        fn mi_malloc_aligned(size: usize, alignment: usize) -> *mut c_void;
        fn mi_zalloc_aligned(size: usize, alignment: usize) -> *mut c_void;
        fn mi_realloc_aligned(p: *mut c_void, newsize: usize, alignment: usize) -> *mut c_void;
        fn mi_free(p: *mut c_void);
    }

    pub struct HostMiMalloc;

    unsafe impl GlobalAlloc for HostMiMalloc {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            mi_malloc_aligned(layout.size(), layout.align()) as *mut u8
        }
        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            mi_zalloc_aligned(layout.size(), layout.align()) as *mut u8
        }
        unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
            mi_free(ptr as *mut c_void)
        }
        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            mi_realloc_aligned(ptr as *mut c_void, new_size, layout.align()) as *mut u8
        }
    }

    #[global_allocator]
    static GLOBAL: HostMiMalloc = HostMiMalloc;
}

/// Used to give each hardware thread a unique ID.
static THREAD_COUNTER: AtomicU64 = AtomicU64::new(0);

thread_local! {
    /// Each thread generates a disjoint set of `u64`s, starting from the hardware thread ID.
    static COUNTER: RefCell<u64> = RefCell::new(THREAD_COUNTER.fetch_add(1, Ordering::AcqRel));
}

/// Generates a fresh `u64` to serve as a variable identifier.
pub fn next_u64() -> u64 {
    COUNTER.with(|c| {
        let mut counter = c.borrow_mut();
        let result = *counter;
        *counter += 128; // We assume there are fewer than 128 hardware threads.
        result
    })
}

/// Represents an index into the `Linked` linked-list data structure for explicit substitutions.
#[derive(Debug, Copy, Clone)]
pub struct DeBruijn(pub u32);

/// Represents an index into an `Entry` of the explicit substitution.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Index {
    Param(usize),
    Let(usize)
}

/// Represents an index to a variable or term in an explicit substitution.
#[derive(Debug, Copy, Clone)]
pub struct DeBruijnIndex(pub DeBruijn, pub Index);

/// An assignment to a metavariable with a `DeBruijnIndex` `head` and arguments `args`.
pub struct Assignment {
    pub head: DeBruijnIndex,
    pub args: Vec<S<Meta>>,

    /// `decl` (redundantly) contains the `Decl` of the `head` symbol in the context Gamma
    pub decl: W<Decl>,

    /// `changes` and `_owned_linked` allow us to return to the previous state during backtracking.
    pub changes: Vec<W<Meta>>,
    pub _owned_linked: Vec<S<Linked>>, // never accessed, only used for ownership.

    /// True if the codomain of `head` is not stuck on a metavariable, for heuristics.
    pub has_rigid_type: bool,
    pub var_type: Option<Type>,

    pub involved: Vec<W<Meta>>
}

/// The core data structure for terms and metavariables, consisting of an `assignment`
/// and additional information required for search, like the `Type` of the metavariable.
pub struct Meta {
    pub assignment: Option<Assignment>,
    /// The local variable context.
    pub gamma: ES,
    /// Constraints that are stuck on this metavariable.
    pub constraints: Vec<Box<dyn Constraint>>,

    /// The `Type` of this metavariable.
    pub typ: Option<Type>,
    /// The bindings introduced by this term.
    pub bindings: W<Bindings>,
    pub from_original_problem: bool,

    pub _owned_bindings: Option<S<Bindings>>, // exclusively for ownership purposes.

    /// Statistics and heuristics information. A cloned metavariable starts with fresh (zero) `stats`,
    /// so each parallel thread accumulates its own delta, and threads are merged by simple addition on join.
    pub stats: SearchInfo,
    pub had_rigid_equation: bool,
    pub branching: f64,
    pub parent: Option<W<Meta>>,

    pub gamma_involved: Vec<W<Meta>>,
    pub typ_involved: Vec<W<Meta>>,
    pub dependence: u32
}

impl Meta {
    /// Creates an unassigned metavariable of a given `Type`.
    pub fn new(typ: Type) -> Self {
        Meta {
            assignment: None,
            gamma: typ.1.clone(),
            constraints: Vec::new(),
            bindings: typ.0.borrow().typ.as_ref().unwrap().borrow().bindings.clone(),
            from_original_problem: false,
            _owned_bindings: None,
            stats: SearchInfo::new_branch(),
            had_rigid_equation: false,
            branching: 1.0,
            parent: None,
            typ: Some(typ),
            gamma_involved: Vec::new(),
            typ_involved: Vec::new(),
            dependence: 0
        }
    }

    /// Checks that the assignment made to `self` does not violate a constraint.
    /// If successful, outputs the new constraints and updates the `changes` of the assignment.
    pub fn test_assignment(&mut self, this: W<Meta>) -> Option<Vec<Box<dyn Constraint>>> {
        let mut new_constraints: Vec<Box<dyn Constraint>> = Vec::new();
        let assn = self.assignment.as_mut().unwrap();

        let premise_type = assn.var_type.as_ref().unwrap();
        let goal_type = self.typ.as_ref().unwrap();

        // check the type of `self` with the codomain of the `var_type
<<<<<<< HEAD
        if (!Equation { premise: premise_type.codomain(), goal: goal_type.codomain(), parent: this.clone() }
=======
        if (!Equation { premise: assn.var_type.as_ref().unwrap().codomain(), goal: self.typ.as_ref().unwrap().codomain(), allow_redexes: false }
>>>>>>> upstream/main
            .reduce(&mut new_constraints, &mut assn.changes, &mut assn._owned_linked)) { return None; }

        if !assn.decl.borrow().redexes.iter().all(|redex|
            RedexConstraint {
                instructions: WVec::new(redex),
                position: 0,
                blame: this.clone(),
            }.reduce(&mut new_constraints, &mut assn.changes, &mut assn._owned_linked)
        ) { return None }

        if !self.constraints.iter().all(|c|
            c.reduce(&mut new_constraints, &mut assn.changes, &mut assn._owned_linked)
        ) { return None }

        // Calculate involved.
        assn.involved.extend(goal_type.1.get_many(goal_type.0.clone(), |tb| &tb.codomain_mvars));
        assn.involved.extend(premise_type.1.get_many(premise_type.0.clone(), |tb| &tb.codomain_mvars));

        return Some(new_constraints);
    }

    pub fn codomain_dependence<const ADD: bool>(&self) {
        for mut mvar in self.typ_involved.iter().cloned() {
            if ADD { mvar.borrow_mut().dependence += 1 } else { mvar.borrow_mut().dependence -= 1 }
        }
    }

    /// Perform an (already tested) assignment.
    pub fn assign(&mut self, mut assn: Assignment, constraints: Vec<Box<dyn Constraint>>) {
        // store constraints with their stuck metavariable
        self.assignment = Some(assn);
        for (item, slot) in constraints.into_iter().zip(self.assignment.as_mut().unwrap().changes.iter_mut()) {
            slot.borrow_mut().constraints.push(item)
        }
        self.codomain_dependence::<false>();
        for arg in &self.assignment.as_ref().unwrap().args {
            arg.borrow().codomain_dependence::<true>();
        }
    }

    /// Unassign the metavariable, returning constraints to their pre-assignment state.
    pub fn unassign(&mut self) -> SearchInfo {
        let mut result = SearchInfo::new_meta();
        for meta in self.assignment.as_mut().unwrap().changes.iter_mut() {
            meta.borrow_mut().constraints.pop().unwrap();
        }
        self.codomain_dependence::<true>();
        for arg in &self.assignment.as_ref().unwrap().args {
            result.add_arg(&arg.borrow().stats);
            arg.borrow().codomain_dependence::<false>();
        }
        self.assignment = None;
        result
    }

    pub fn pop_recursive(&mut self) {
        if let Some(assn) = &mut self.assignment {
            for mvar in assn.args.iter_mut() {
                mvar.borrow_mut().pop_recursive();
            }
            for meta in assn.changes.iter_mut() {
                meta.borrow_mut().constraints.pop();
            }
        }
    }

    pub fn unassign_recursive(&mut self) {
        if let Some(assn) = &mut self.assignment {
            for mvar in assn.args.iter_mut() {
                mvar.borrow_mut().unassign_recursive();
            }
            self.assignment = None;
        }
    }
}

pub trait Constraint: std::any::Any {
    /// Propagate the constraint on the basis of new assignments.
    fn reduce(&self, constraints: &mut Vec<Box<dyn Constraint>>, changes: &mut Vec<W<Meta>>,
              owned_linked: &mut Vec<S<Linked>>) -> bool;

    /// Whether this constraint enforces an assignment on the stuck metavariable.
    fn rigid(&self) -> bool { false }

    /// The metavariables whose assignments might interact with this constraint.
    fn involved(&self) -> Box<dyn Iterator<Item = W<Meta>> + '_>;
}

/// A definitional (judgmental) equality between two `Term`s.
#[derive(Clone)]
pub struct Equation {
    /// `premise` is a subterm of the `codomain` of the `Type` of a variable
    pub premise: Term,
    /// `goal` is a subterm of the `codomain` of the `Type` of a metavariable
    pub goal: Term,
<<<<<<< HEAD

    pub parent: W<Meta>
=======
    pub allow_redexes: bool
>>>>>>> upstream/main
}

#[derive(Clone)]
pub struct RedexConstraint {
    pub instructions: WVec<Instruction>,
    pub position: usize,
    /// The metavariable this constraint is currently walking from.
    pub blame: W<Meta>
}

impl Constraint for RedexConstraint {
    fn reduce(&self, constraints: &mut Vec<Box<dyn Constraint>>, changes: &mut Vec<W<Meta>>,
              _owned_linked: &mut Vec<S<Linked>>) -> bool {
        let mut blame = self.blame.clone();
        let mut i = self.position;
        while let Some(assn) = &blame.borrow().assignment {
            if !assn.decl.eq(&self.instructions[i].decl) {
                return true;
            }
            if i == self.instructions.len() - 1 {
                return false;
            }
            for _ in 0..self.instructions[i].parents {
                blame = blame.borrow().parent.as_ref().unwrap().clone();
            }
            blame = blame.borrow().assignment.as_ref().unwrap().args[self.instructions[i].child].downgrade();
            i += 1;
        }
        constraints.push(Box::new(RedexConstraint {
            instructions: self.instructions.clone(),
            position: i,
            blame: blame.clone(),
        }));
        changes.push(blame);
        return true
    }

    fn involved(&self) -> Box<dyn Iterator<Item = W<Meta>> + '_> {
        Box::new(iter::empty()) // TODO
    }
}


impl Constraint for Equation {
    /// Break down the equation into equations that are stuck on metavariables, added to `constraints`.
    /// Returns false if the equation is violated.
    fn reduce(&self, constraints: &mut Vec<Box<dyn Constraint>>, changes: &mut Vec<W<Meta>>,
              owned_linked: &mut Vec<S<Linked>>) -> bool {
        if owned_linked.len() > 1000 { return false }
        // Reduce both sides of the equation.
        match self.premise.whnf::<true, ()>(owned_linked, &mut (), self.allow_redexes) {
            WHNF(premise, Head::Var(lhs)) => {
                match self.goal.whnf::<true, ()>(owned_linked, &mut (), self.allow_redexes) {
                    WHNF(goal, Head::Var(rhs)) => {
                        // If the head symbols are not equal, the equation is violated.
                        if !lhs.eq(&rhs) { return false }

                        // Identifier for the variables bound by the arguments of premise and goal.
                        let var_id = next_u64();

                        // Check that the arguments of premise and goal are equal.
                        (0..premise.base.borrow().assignment.as_ref().unwrap().args.len()).all(|i|
                            Equation {
                                premise: premise.arg(i, Entry::vars(var_id), owned_linked),
<<<<<<< HEAD
                                goal: goal.arg(i, Entry::vars(var_id), owned_linked), 
                                parent: self.parent.clone()
=======
                                goal: goal.arg(i, Entry::vars(var_id), owned_linked),
                                allow_redexes: self.allow_redexes
>>>>>>> upstream/main
                            }.reduce(constraints, changes, owned_linked)
                        )
                    }
                    WHNF(goal, Head::Meta(rhs)) => {
                        // goal is stuck, add an equation associated with goal_meta.
<<<<<<< HEAD
                        constraints.push(Box::new(Equation { premise, goal, parent: self.parent.clone() }));
=======
                        constraints.push(Box::new(Equation { premise, goal, allow_redexes: self.allow_redexes }));
>>>>>>> upstream/main
                        changes.push(rhs);
                        true
                    }
                }
            }
            WHNF(premise, Head::Meta(lhs)) => {
                // premise is stuck, add an equation associated with premise_meta.
<<<<<<< HEAD
                constraints.push(Box::new(Equation { premise, goal: self.goal.clone(), parent: self.parent.clone() }));
=======
                constraints.push(Box::new(Equation { premise, goal: self.goal.clone(), allow_redexes: self.allow_redexes }));
>>>>>>> upstream/main
                changes.push(lhs);
                true
            }
        }
    }

    fn rigid(&self) -> bool {
        matches!(self.premise.whnf::<true, ()>(&mut Vec::new(), &mut (), self.allow_redexes).1, Head::Var(_)) ||
        matches!(self.goal.whnf::<true, ()>(&mut Vec::new(), &mut (), self.allow_redexes).1, Head::Var(_))
    }

    fn involved(&self) -> Box<dyn Iterator<Item = W<Meta>> + '_> {
        Box::new(self.parent.borrow().assignment
            .as_ref().unwrap().involved.iter().cloned())
    }
}


/// A substitution with a list of terms, all with the same explicit substitution.
/// Note that the explicit substitution does not contain the local variables unique to each
/// element of the vector.
#[derive(Clone)]
pub struct Subst(pub WVec<S<Meta>>, pub ES);

impl Subst {
    /// Obtain `Term` `i` from the substitution, using `entry` for the local variables.
    pub fn get(&self, i: usize, entry: Entry, owned_linked: &mut Vec<S<Linked>>) -> Term {
        let base = self.0[i].downgrade();
        let bindings = base.borrow().bindings.clone();
        Term { es: self.1.append(Node { entry, bindings }, owned_linked), base }
    }
}

/// A list indexed by `Index`.
pub struct Bindings {
    pub params: Vec<S<Decl>>,
    pub lets: Vec<S<Decl>>
}

impl std::ops::Index<Index> for Bindings {
    type Output = S<Decl>;

    fn index(&self, index: Index) -> &Self::Output {
        match index {
            Param(i) => &self.params[i],
            Let(i) => &self.lets[i]
        }
    }
}

impl Bindings {
    /// We iterate over params first, as free variables are generally more important than consts.
    /// We iterate over params and lets in reverse order to prioritize dependently typed variables.
    pub fn iter(indexed: &Bindings) -> impl Iterator<Item = Index> + '_ {
        let params_iter = (0..indexed.params.len()).rev().map(Param);
        let lets_iter = (0..indexed.lets.len()).rev().map(Let);
        params_iter.chain(lets_iter)
    }
}

pub struct Instruction {
    pub decl: W<Decl>,
    pub parents: u32,
    pub child: usize
}

pub struct Symbol {
    pub decl: W<Decl>,
    pub children: Vec<usize>,
    pub bindings: S<Bindings>
}

pub struct Rule {
    pub pattern: Vec<Option<Symbol>>,
    pub replacement: S<Meta>,
    pub attribution: Vec<String>
}

<<<<<<< HEAD
/// The `name` and `value` of a variable in the original input problem.
pub struct Bind {
    pub name: String,
    pub rules: Vec<Rule>,
    pub redexes: Vec<Vec<Instruction>>,
    pub polarity: Polarity,

    pub owned_bindings: Vec<S<Indexed<S<Bind>>>>
}

impl Bind {
    pub fn new(name: String, polarity: Polarity) -> Self {
        Bind {
=======
/// One step in a path through the problem, viewed as nested declarations and expressions:
/// a declaration (a param, a let, or the root problem itself) has a `Type`, and a param or let has `Rule(i)`s;
/// a rule has an `LHS` and `RHS` expression; an expression (an `IRExpr` together
/// with its spine) declares `Param(i)`s and `Let(i)`s and applies its head to `Arg(i)`s.
/// The path of an expression also identifies the occurrence of its head symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Position {
    Type,
    Rule(usize),
    LHS,
    RHS,
    Param(usize),
    Let(usize),
    Arg(usize),
}

/// A variable declared in the original input problem, with its `name`, optional `typ`, and equations:
/// a let's equations are compiled into `rules` and `redexes`, and a param's into `constraints`.
pub struct Decl {
    pub name: String,
    pub constraints: Vec<(S<Meta>, S<Meta>, bool)>,
    pub rules: Vec<Rule>,
    pub redexes: Vec<Vec<Instruction>>,
    pub typ: Option<S<Meta>>,
    pub position: Vec<Position>,
    pub _owned_bindings: Vec<S<Bindings>>,
    pub index: usize
}

impl Decl {
    pub fn new(name: String, position: Vec<Position>) -> Self {
        Decl {
>>>>>>> upstream/main
            name,
            constraints: Vec::new(),
            rules: Vec::new(),
            redexes: Vec::new(),
<<<<<<< HEAD
            polarity,
            owned_bindings: Vec::new()
=======
            typ: None,
            position,
            _owned_bindings: Vec::new(),
            index: usize::MAX
>>>>>>> upstream/main
        }
    }
}

/// An explicit substitution entry, consisting of identifiers for the params and lets
/// and optionally a substitution or typing context. 
#[derive(Clone)]
pub struct Entry {
    pub params_id: u64,
    pub lets_id: u64,
    pub subst: Option<Subst>,
    pub context: Option<Type>
}

impl Entry {
    /// Creates a substitution entry.
    pub fn subst(subst: Subst) -> Self {
        Self {
            params_id: next_u64(),
            lets_id: next_u64(),
            subst: Some(subst),
            context: None
        }
    }

    /// Creates a variable entry.
    pub fn vars(params_id: u64) -> Self {
        Self {
            params_id,
            lets_id: next_u64(),
            subst: None,
            context: None
        }
    }
}

/// An `entry` accompanied with the associated `bindings` from the original problem. 
pub struct Node {
    pub entry: Entry,
    pub bindings: W<Bindings>,
}

/// A linked list of `Node`
pub struct Linked {
    pub tail: Option<W<Linked>>,
    pub node: Node
}

/// An Explicit Substitution, associating a `DeBruijnIndex` with a `Var` or `Term`.
#[derive(Clone)]
pub struct ES {
    pub linked: Option<W<Linked>>
}

impl ES {
    /// An empty explicit substitution.
    pub fn new() -> Self {
        ES { linked: None }
    }

    /// Append a `Node` to the explicit substitution. 
    /// The caller is responsible for keeping `owned_linked` around as long as they wish to use the ES.
    pub fn append(&self, node: Node, owned_linked: &mut Vec<S<Linked>>) -> ES {
        // Zero-size optimization, when nothing needs to be added.
        if node.bindings.borrow().params.len() == 0 && node.bindings.borrow().lets.len() == 0 {
            return self.clone() // ES is just a pointer.
        }
        let link = S::new(Linked { tail: self.linked.to_owned(), node });
        let weak = link.downgrade();
        // Pass the ownership.
        owned_linked.push(link);
        ES { linked: Some(weak) }
    }
    
    /// Returns the sublist rooted at node `db`.
    pub fn sub_es(&self, db: DeBruijn) -> ES {
        let mut curr = self.linked.as_ref().unwrap();
        for _ in 0..db.0 {
            curr = curr.borrow().tail.as_ref().expect("Index out of bounds!");
        }
        ES { linked: Some(curr.to_owned()) }
    }

    /// Gets the variable at the root of this ES at the given `index`
    pub fn get_var(&self, index: Index) -> Var {
        let node = &self.linked.as_ref().unwrap().borrow().node;
        let entry_id = match index {
            Param(_) => node.entry.params_id,
            Let(_) => node.entry.lets_id
        };

        Var {
            decl: node.bindings.borrow()[index].downgrade(),
            index,
            entry_id
        }
    }

    /// Returns an iterator of `DeBruijnIndex` in this `ES``, along with the `Linked` they are rooted at.
    pub fn iter(&self) -> impl Iterator<Item = (DeBruijnIndex, W<Linked>, Var)> {
        iter::successors(self.linked.clone(), |node| 
            node.borrow().tail.clone() // Iterate over the linked list.
        ).enumerate().flat_map(move |(db, node)| {
<<<<<<< HEAD
            let indices: Vec<Index> = Indexed::iter(node.borrow().node.bindings.borrow()).collect();
            indices.into_iter().map(move |item| 
                (DeBruijnIndex(DeBruijn(db as u32), item), node.clone(), Var {
                    entry_id: if matches!(item, Param(_)) {node.borrow().node.entry.params_id} else {node.borrow().node.entry.lets_id}, 
                    index: item, bind: node.borrow().node.bindings.borrow()[item].downgrade(),
                }))
        })
    }

    /// Finds the `DeBruijnIndex` and `Bind` with a certain `name` in this `ES`.
    pub fn index_of(&self, name: &String) -> Option<(DeBruijnIndex, Var)> {
        self.iter().find(|(_db, _linked, var)| &var.bind.borrow().name == name)
            .map(|(db, _linked, var)| { (db, var) })
    }

    /// The number of `Linked` nodes (explicit-substitution entries) in this `ES`.
    pub fn length(&self) -> usize {
        iter::successors(self.linked.clone(), |node|
            node.borrow().tail.clone() // Iterate over the linked list.
        ).count()
    }

    pub fn get_many(&self, tb: W<TypeBase>, indices: fn(&TypeBase) -> &Vec<Vec<usize>>) -> impl Iterator<Item = W<Meta>> {
        assert_eq!(self.length(), indices(tb.borrow()).len(),
            "get_many: ES length does not match the input vector length");
        iter::successors(self.linked.clone(), |node|
            node.borrow().tail.clone() // Iterate over the linked list.
        ).enumerate().flat_map(move |(i, linked)| {
            let tb = tb.clone();
            (0..indices(tb.borrow())[i].len()).map(move |k| {
                let j = indices(tb.borrow())[i][k];
                linked.borrow().node.entry.subst.as_ref().expect("not a subst!").0[j].downgrade()
            })
        })
    }

    pub fn involved(&self) -> impl Iterator<Item = W<Meta>> {
        iter::successors(self.linked.clone(), |node|
            node.borrow().tail.clone() // Iterate over the linked list.
        ).filter_map(|linked| linked.borrow().node.entry.context.clone())
        .flat_map(|typ| typ.1.get_many(typ.0, |tb| &tb.types_mvars))
=======
            let indices: Vec<Index> = Bindings::iter(node.borrow().node.bindings.borrow()).collect();
            indices.into_iter().map(move |item| (DeBruijnIndex(DeBruijn(db as u32), item), node.clone()))
        })
    }

    /// Finds the `DeBruijnIndex` and `Decl` with a certain `name` in this `ES`.
    pub fn index_of(&self, name: &String) -> Option<(DeBruijnIndex, W<Decl>)> {
        self.iter().find(|(db, linked)| &linked.borrow().node.bindings.borrow()[db.1].borrow().name == name)
            .map(|(db, linked)| (db, linked.borrow().node.bindings.borrow()[db.1].downgrade()))
>>>>>>> upstream/main
    }
}

/// A Term is a `DeBruijnIndex`-ed `base` with an explicit substitution `es` 
/// that associates a `DeBruijnIndex` with a variable or term.
#[derive(Clone)]
pub struct Term {
    pub base: W<Meta>,
    pub es: ES
}

pub enum Head {
    Var(Var),
    Meta(W<Meta>)
}

/// A Term in weak head normal form, with the variable at the head, or the metavariable reduction is stuck on.
/// We allow both the variable and metavariable to be present for when we are stuck on the major argument of a recursor.
pub struct WHNF(pub Term, pub Head);

pub struct Matcher<'a> {
    pub pattern: Iter<'a, Option<Symbol>>,
    pub replacement: Term,
    pub rule: &'a Rule
}

pub trait Attribution {
    fn attribute(&mut self, s: &Rule);
}

impl Attribution for () {
    fn attribute(&mut self, _: &Rule) {}
}

impl Attribution for Vec<String> {
    fn attribute(&mut self, s: &Rule) {
        self.append(&mut s.attribution.clone());
    }
}

impl Term {
    /// Get the `i`th argument, applied with `entry`.
    pub fn arg(&self, i: usize, entry: Entry, owned_linked: &mut Vec<S<Linked>>) -> Term {
        let base = self.base.borrow().assignment.as_ref().unwrap().args[i].downgrade();
        Term { es: self.es.append(Node { entry, bindings: base.borrow().bindings.clone() }, owned_linked), base }
    }

<<<<<<< HEAD
    /// Computes the weak head normal form. 
    pub fn whnf<const RULES: bool, C: Attribution>(&self, owned_linked: &mut Vec<S<Linked>>, attribution: &mut C) -> WHNF {
=======
    /// Computes the weak head normal form.
    pub fn whnf<const RULES: bool, C: Attribution>(&self, owned_linked: &mut Vec<S<Linked>>, attribution: &mut C, allow_redexes: bool) -> WHNF {
        guard_overflow();
>>>>>>> upstream/main
        if let Some(assn) = &self.base.borrow().assignment {
            let es = self.es.sub_es(assn.head.0);

            // If there is a term at the head, recursively reduce it. Otherwise, the variable is the head symbol.
            if let Param(i) = assn.head.1 {
                if let Some(subst) = &es.linked.as_ref().unwrap().borrow().node.entry.subst {
                    // If there is a substitution, and the index is a parameter, return the associated term in the substitution.
                    let term = subst.get(i, Entry::subst(Subst(WVec::new(&assn.args), self.es.clone())), owned_linked);
                    return term.whnf::<RULES, C>(owned_linked, attribution, allow_redexes);
                }
            }

            let var = es.get_var(assn.head.1);
            let decl = var.decl.clone();
            let whnf = WHNF(self.clone(), Head::Var(var));
            if RULES && !decl.borrow().rules.is_empty() {
                let mut matchers = decl.borrow().rules.iter().map(|rule| Matcher {
                    pattern: rule.pattern.iter(),
                    replacement: Term { base: rule.replacement.downgrade(), es: es.clone() },
                    rule: &rule
                }).collect();
                let mut stuck : Option<W<Meta>> = None;
                let matched = whnf.pattern_match(&mut matchers, owned_linked, attribution, allow_redexes || whnf.0.base.borrow().from_original_problem, allow_redexes, &mut stuck);
                if let ControlFlow::Break((term, rule)) = matched {
                    attribution.attribute(rule);
                    return term.whnf::<RULES, C>(owned_linked, attribution, allow_redexes);
                }
                if let Some(meta) = stuck {
                    return WHNF(self.clone(), Head::Meta(meta));
                }
            }
            whnf
        } else {
            WHNF(self.clone(), Head::Meta(self.base.clone()))
        }
    }
}

impl <'a> WHNF {
<<<<<<< HEAD
    fn pattern_match<C: Attribution>(&self, patterns: &mut Vec<Matcher<'a>>, owned_linked: &mut Vec<S<Linked>>, attribution: &mut C, can_stuck: bool, stuck: &mut Option<W<Meta>>) -> ControlFlow<(Term, &'a Rule)> {
=======
    /// `can_stuck` is whether a metavariable blocking a match makes the term stuck,
    /// and `allow_redexes` is passed on to the reduction of arguments.
    fn pattern_match<C: Attribution>(&self, patterns: &mut Vec<Matcher<'a>>, owned_linked: &mut Vec<S<Linked>>, attribution: &mut C,
        can_stuck: bool, allow_redexes: bool, stuck: &mut Option<W<Meta>>) -> ControlFlow<(Term, &'a Rule)> {
        guard_overflow();
>>>>>>> upstream/main
        match &self.1 {
            Head::Meta(meta) => {
                patterns.retain_mut(|matcher| 
                    matcher.pattern.next().unwrap().is_none()
                );
                if can_stuck {
                    stuck.replace(meta.clone());
                }
                ControlFlow::Continue(())
            }
            Head::Var(var) => {
                let mut recursive = Vec::new();
                let mut ordering: Option<&Vec<usize>> = None;
                
                for i in (0..patterns.len()).rev() {
                    if let Some(symbol) = patterns[i].pattern.next().unwrap() {
<<<<<<< HEAD
                        let mut matcher = patterns.swap_remove(i);
                        if symbol.bind.eq(&var.bind) {
=======
                        let mut matcher = patterns.remove(i);
                        if symbol.decl.eq(&var.decl) {
>>>>>>> upstream/main
                            ordering = Some(&symbol.children);
                            matcher.replacement.es = matcher.replacement.es.append(Node {
                                entry: Entry::subst(Subst(WVec::new(&self.0.base.borrow().assignment.as_ref().unwrap().args), self.0.es.clone())),
                                bindings: symbol.bindings.downgrade()
                            }, owned_linked);
                            if matcher.pattern.len() == 0 {
                                return ControlFlow::Break((matcher.replacement.clone(), matcher.rule));
                            }
                            recursive.push(matcher);
                        }
                    }
                }

                if let Some(ordering) = ordering {
                    for &i in ordering {
                        let arg = self.0.arg(i, Entry::vars(next_u64()), owned_linked);
                        arg.whnf::<true, C>(owned_linked, attribution, allow_redexes).pattern_match(&mut recursive, owned_linked, attribution, can_stuck, allow_redexes, stuck)?;
                        if recursive.is_empty() { break; }
                    }
                }

                patterns.append(&mut recursive); // TODO this changes the order
                ControlFlow::Continue(())
            }
        }
    }
}

<<<<<<< HEAD
/// A `DeBruijnIndex`-ed type, with a `codomain` (return type)
/// and parameter/let `types` 
pub struct TypeBase {
    pub codomain: S<Meta>,
    pub types: S<Indexed<Option<S<TypeBase>>>>,
    
    /// For negative `TypeBases`, all negative indices used in the `codomain`.
    /// For positive `TypeBases`, all negative indices used in `types`.
    pub codomain_mvars: Vec<Vec<usize>>,
    pub types_mvars: Vec<Vec<usize>>
=======
#[derive(Clone, Copy)]
pub enum Polarity { 
    Premise, Goal
}

impl Polarity {
    pub fn opposite(self) -> Polarity {
        match self {
            Polarity::Premise => Polarity::Goal,
            Polarity::Goal => Polarity::Premise
        }
    }
>>>>>>> upstream/main
}

impl Meta {
    /// Create new metavariables to fill the parameters of this type, whose `bindings` declare them.
    pub fn args_metas(&self, parent: Option<W<Meta>>) -> Vec<S<Meta>> {
        let arity = self.bindings.borrow().params.len();
        let mut args = Vec::with_capacity(arity);
        for i in 0..arity {
            args.push(S::new(Meta {
                assignment: None,
                typ: None,
                gamma: ES::new(),
                constraints: Vec::new(),
                bindings: self.bindings.borrow()[Index::Param(i)].borrow().typ.as_ref().unwrap().borrow().bindings.clone(),
                from_original_problem: false,
                _owned_bindings: None,
                stats: SearchInfo::new_branch(),
                had_rigid_equation: false,
                branching: 1.0,
                parent: parent.clone(),
                gamma_involved: Vec::new(),
                typ_involved: Vec::new(),
                dependence: 0
            }))
        }
        args
    }
}

/// A Type is the `DeBruijnIndex`-ed type of a `Decl` with an explicit substitution `es`
/// that associates a `DeBruijnIndex` with a variable or term.
/// The `Decl` is the variable in the original problem that has this `Type`.
#[derive(Clone)]
pub struct Type(pub W<Decl>, pub ES);

impl Type {
    /// Get the return type, as a `Term`.
    pub fn codomain(&self) -> Term {
        Term { base: self.0.borrow().typ.as_ref().unwrap().downgrade(), es: self.1.clone() }
    }

    /// Get the `i`th parameter type, specialized to `entry`.
    pub fn get(&self, i: Index, entry: Entry, owned_linked: &mut Vec<S<Linked>>) -> Type {
        let base = &self.0.borrow().typ.as_ref().unwrap().borrow().bindings.borrow()[i];
        Type(
            base.downgrade(), 
            self.1.append(Node {entry, bindings: base.borrow().typ.as_ref().unwrap().borrow().bindings.clone() }, owned_linked),
        )
    }
}

/// A variable from entry `entry_id` at position `index`,
/// associated with `bind` from the original problem. 
pub struct Var {
    pub entry_id: u64,
    index: Index,
    pub decl: W<Decl>
}

impl PartialEq for Var {
    /// Two variables from the same entry at the same position are equal.
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.entry_id == other.entry_id
    }
}

impl Eq for Var {}
impl Hash for Var {
    fn hash<H>(&self, h: &mut H) where H: Hasher { 
        h.write_u64(self.entry_id);
        match self.index {
            Param(i) => {
                h.write_u8(0);
                h.write_usize(i);
            }
            Let(i) => {
                h.write_u8(255);
                h.write_usize(i);
            }
        }
    }
}

#[derive(Clone, Copy)]
pub enum Polarity { Goal, Premise }

impl Polarity {
    pub fn opposite(&self) -> Polarity {
        match self {
            Polarity::Goal => Polarity::Premise,
            Polarity::Premise => Polarity::Goal
        }
    }
}