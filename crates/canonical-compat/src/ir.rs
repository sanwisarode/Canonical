use canonical_core::core::*;
use canonical_core::memory::{S, W};
<<<<<<< HEAD
use canonical_core::core::Index::Param;
=======
use canonical_core::ai::Tokenization;
>>>>>>> upstream/main
use canonical_core::search::test;
use canonical_core::compiler::compile;
use canonical_core::heuristic::reset_weights;
use std::fmt;
use serde::{Serialize, Deserialize};
use std::fs::File;
use crate::reduction::*;
use canonical_core::stats::SearchInfo;
use std::collections::HashSet;
use std::any::Any;

/// Render the metavariables involved with `meta`, each labeled with its name and the constraints stuck on it.
// fn involved_html(meta: W<Meta>) -> String {
//     let mut seen = HashSet::new();
//     canonical_core::independence::involved(meta).into_iter()
//         .filter(|m| seen.insert(m.borrow() as *const Meta as usize))
//         .map(|m| {
//             // Argument/substitution metavariables have no type (see `to_body`), so don't assume one.
//             let name = match m.borrow().typ.as_ref() {
//                 Some(typ) => "?&NoBreak;".to_string() + &typ.2.borrow().name,
//                 None => "?".to_string(),
//             };
//             format!("<div class='involved'><span class='meta'>{name}</span></div>")
//         })
//         .collect()
// }

/// Render a constraint stuck on a metavariable for the debug tooltip, recovering its concrete type.
fn constraint_html(c: &dyn Constraint, owned_linked: &mut Vec<S<Linked>>) -> String {
    if let Some(eqn) = (c as &dyn Any).downcast_ref::<Equation>() {
        let lhs = IRSpine::from_body::<true>(eqn.premise.whnf::<true, ()>(owned_linked, &mut (), eqn.allow_redexes), false);
        let rhs = IRSpine::from_body::<true>(eqn.goal.whnf::<true, ()>(owned_linked, &mut (), eqn.allow_redexes), false);
        format!("<div class='constraint'>{lhs} ≡ {rhs}</div>")
    } else if let Some(redex) = (c as &dyn Any).downcast_ref::<RedexConstraint>() {
        let path = (redex.position..redex.instructions.len())
            .map(|i| redex.instructions[i].decl.borrow().name.clone())
            .collect::<Vec<_>>()
            .join(" → ");
        format!("<div class='constraint'>redex: {path}</div>")
    } else {
        String::new()
    }
}

#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IREquation {
    pub lhs: IRSpine,
    pub rhs: IRSpine,
    #[serde(skip)]
    pub attribution: Vec<String>,
    pub is_redex: bool
}

/// A declaration, with a variable `name`, optional `typ`, and defining `equations`.
#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRDecl {
    pub name: String,
    pub typ: Option<IRExpr>,
    pub equations: Vec<IREquation>
}

#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRSpine {
    pub head: String,
    pub args: Vec<IRExpr>,
    #[serde(skip)]
    pub premise_rules: Vec<String>
}

/// An expression is an n-ary, β-normal, η-long λ expression:
/// `λ params lets . head args`.
/// Read as a type, it is an n-ary Π-type with codomain `spine`,
/// where the declarations carry the domain types.
#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRExpr {
    pub params: Vec<IRDecl>,
    pub lets: Vec<IRDecl>,
    pub spine: IRSpine,
    #[serde(skip)]
    pub goal_rules: Vec<String>
}

/// `position` extended with `steps`.
pub(crate) fn extend(position: &[Position], steps: &[Position]) -> Vec<Position> {
    [position, steps].concat()
}

<<<<<<< HEAD
impl IRVar {
    pub fn to_bind(&self, polarity: Polarity) -> Bind {
        Bind {
            name: self.name.clone(),
            rules: Vec::new(),
            redexes: Vec::new(),
            polarity,
            owned_bindings: Vec::new()
=======
impl IRDecl {
    pub fn to_decl(&self, position: Vec<Position>) -> Decl { Decl::new(self.name.clone(), position) }

    /// Translate this declaration, compiling `equations` and `typ` into `decl`.
    /// Equations on a let (`LET`) define reduction, as rewrite rules and redexes;
    /// equations on a param constrain the instantiation of its variables, checked as `Equation`s.
    fn translate<const LET: bool>(&self, decl: &mut S<Decl>, es: &ES, owned_linked: &mut Vec<S<Linked>>,
        position: &[Position], tokens: &mut Tokenization, polarity: Option<Polarity>) {
        if LET {
            let mut owned_bindings = Vec::new();
            decl.borrow_mut().rules = to_rules(&self.equations, es, owned_linked, &mut owned_bindings, position, tokens);
            decl.borrow_mut().redexes = to_redexes(&self.equations, es);
            decl.borrow_mut()._owned_bindings = owned_bindings;
        } else {
            decl.borrow_mut().constraints = self.equations.iter().enumerate().map(|(i, c)| (
                S::new(c.lhs.to_body(es.clone(), S::new(Bindings { params: Vec::new(), lets: Vec::new() }), Vec::new(), 
                    &extend(position, &[Position::Rule(i), Position::LHS]), tokens)),
                S::new(c.rhs.to_body(es.clone(), S::new(Bindings { params: Vec::new(), lets: Vec::new() }), Vec::new(),
                    &extend(position, &[Position::Rule(i), Position::RHS]), tokens)),
                c.is_redex
            )).collect();
>>>>>>> upstream/main
        }
        if let (Some(polarity), Some(typ)) = (polarity, &self.typ) {
            let list = match polarity {
                Polarity::Goal => &mut tokens.goals,
                Polarity::Premise => &mut tokens.premises
            };
            decl.borrow_mut().index = list.len();
            list.push(decl.downgrade());
            decl.borrow_mut().typ = Some(typ.to_expr(es, &extend(position, &[Position::Type]), tokens, Some(polarity)));
        } else {
            tokens.tokens.push((position.to_vec(), decl.downgrade()));
        }
    }

    /// Translate this declaration into a `Decl` to be solved for by a `Prover` and compile the problem.
    pub fn to_problem(&self) -> (S<Decl>, Tokenization) {
        assert!(self.typ.is_some(), "Declaration {} has no type.", self.name);
        let mut decl = S::new(self.to_decl(Vec::new()));
        let mut tokens = Tokenization::default();
        self.translate::<false>(&mut decl, &ES::new(), &mut Vec::new(), &[], &mut tokens, Some(Polarity::Goal));
        reset_weights();
        compile(Type(decl.downgrade(), ES::new()));
        (decl, tokens)
    }
}

fn get_rules(term: &Term) -> Vec<String> {
    let mut attribution = Vec::new();
    let mut owned_linked = Vec::new();
    _get_rules(term, &mut attribution, &mut owned_linked);
    attribution
}

fn _get_rules(term: &Term, attribution: &mut Vec<String>, owned_linked: &mut Vec<S<Linked>>) {
    let whnf = term.whnf::<true, Vec<String>>(owned_linked, attribution, false);
    if whnf.0.base.borrow().assignment.is_some() {
        let len = whnf.0.base.borrow().assignment.as_ref().unwrap().args.len();
        for i in 0..len {
            let arg = whnf.0.arg(i, Entry::vars(next_u64()), owned_linked);
            _get_rules(&arg, attribution, owned_linked);
        }
    }
}

<<<<<<< HEAD
/// Create a `Bind` with the `preferred_name`, appending a suffix such that it is not contained in `es`.
fn disambiguate_bind(preferred_name: &String, es: &ES, polarity: Polarity) -> Bind {
=======
/// Create a `Decl` with the `preferred_name`, appending a suffix such that it is not contained in `es`.
fn disambiguate_decl(preferred_name: &String, es: &ES) -> Decl {
>>>>>>> upstream/main
    let mut count = 0;
    let mut name = preferred_name.clone();
    while es.index_of( &name).is_some() {
        count += 1;
        name = preferred_name.clone() + &count.to_string();
    }
<<<<<<< HEAD
    Bind::new(name, polarity)
}

/// Construct a copy of `bindings` such that the names are not already in `es`.
fn disambiguate(bindings: W<Indexed<S<Bind>>>, es: &ES, polarity: Polarity) -> Indexed<S<Bind>> {
    let params = bindings.borrow().params.iter().map(
        |b| S::new(disambiguate_bind(&b.borrow().name, es, polarity))).collect();
    let lets = bindings.borrow().lets.iter().map(
        |b| S::new(disambiguate_bind(&b.borrow().name, es, polarity))).collect();
    Indexed { params, lets }
=======
    Decl::new(name, Vec::new())
}

/// Construct a copy of `bindings` such that the names are not already in `es`.
fn disambiguate(bindings: W<Bindings>, es: &ES) -> Bindings {
    let params = bindings.borrow().params.iter().map(
        |b| S::new(disambiguate_decl(&b.borrow().name, es))).collect();
    let lets = bindings.borrow().lets.iter().map(
        |b| S::new(disambiguate_decl(&b.borrow().name, es))).collect();
    Bindings { params, lets }
>>>>>>> upstream/main
}

impl IRSpine {
    pub fn from_body<const RULES: bool>(WHNF(whnf, head): WHNF, html: bool) -> IRSpine {
        let mut owned_linked = Vec::new();
            
        match &head {
            Head::Meta(meta) => {
                if html {
                    IRSpine { head: Self::meta_html(meta.clone()), args: Vec::new(), premise_rules: Vec::new() }
                } else {
                    Self::from_meta::<RULES>(whnf, meta.clone())
                }
            }
            Head::Var(var) => {
                let mut _owned_bindings = Vec::new();

                let args = whnf.base.borrow().assignment.as_ref().unwrap().args.iter().map(|arg| {
                    let bindings = S::new(disambiguate(arg.borrow().bindings.clone(), &whnf.es, Polarity::Goal));
                    let wbindings = bindings.downgrade();
                    let es = whnf.es.append(Node {
                        entry: Entry::vars(next_u64()),
                        bindings: wbindings.clone()
                    }, &mut owned_linked);
                    _owned_bindings.push(bindings);
                    IRExpr::from_lambda::<RULES>(Term { base: arg.downgrade(), es }, wbindings.clone(), html)
                }).collect();

                IRSpine {
                    head: var.decl.borrow().name.clone(),
                    args,
                    premise_rules: whnf.base.borrow().assignment.as_ref().unwrap().var_type.as_ref().map(|typ| get_rules(&typ.codomain())).unwrap_or_default()
                }
            }
        }
    }

    fn from_meta<const RULES: bool>(term: Term, stuck: W<Meta>) -> IRSpine {
        let mut args = Vec::new();
        if !stuck.borrow().bindings.borrow().params.is_empty() {
            if let Some(subst) = &term.es.linked.as_ref().unwrap().borrow().node.entry.subst {
                let mut _owned_bindings = Vec::new();
                for i in 0..subst.0.len() {
                    let mut owned_linked = Vec::new();
                    let arg = subst.0[i].downgrade();
                    let bindings = S::new(disambiguate(arg.borrow().bindings.clone(), &subst.1, Polarity::Goal));
                    let wbindings = bindings.downgrade();
                    let es = subst.1.append(Node {
                        entry: Entry::vars(next_u64()),
                        bindings: wbindings.clone()
                    }, &mut owned_linked);
                    _owned_bindings.push(bindings);
                    args.push(IRExpr::from_lambda::<RULES>(Term { base: arg, es }, wbindings.clone(), false))
                }
            }
        }
        IRSpine {
            head: "?&NoBreak;".to_string() + &stuck.borrow().typ.as_ref().unwrap().0.borrow().name,
            args,
            premise_rules: Vec::new()
        }
    }

    fn meta_html(meta: W<Meta>) -> String {
        let varname = "?&NoBreak;".to_string() + &meta.borrow().typ.as_ref().unwrap().0.borrow().name;
        let meta_id = meta.borrow() as *const Meta as usize;

        let options = meta.borrow().gamma.iter().filter_map(|(db, linked, _)| {
            if let Some(Some(result)) = test(db, linked, meta.clone()) {
                let name = result.0.decl.borrow().name.clone();

                let (index, def) = match db.1 {
                    Index::Param(i) => (i, false),
                    Index::Let(i) => (i, true)
                };
                let debruijn = db.0.0;
                
                return Some(format!("<button class='option' onclick='assign({meta_id}, {debruijn}, {index}, {def})'>{name}</button>"));
            }
            None
        }).reduce(|a, b| format!("{a}</br>{b}")).unwrap_or("<div class='fail'>No Options</div>".to_string());
        let mut owned_linked = Vec::new();
        let typ = IRSpine::from_body::<true>(meta.borrow().typ.as_ref().unwrap().codomain().whnf::<true, ()>(&mut owned_linked, &mut (), false), false);

        let own = meta.borrow().constraints.iter()
            .map(|c| constraint_html(c.as_ref(), &mut owned_linked))
            .fold("".to_string(), |a, b| a + &b);
        // Also surface the metavariables involved with this one, each with their own constraints.
        let inner = own; //+ &involved_html(meta.clone());
        let constraints = if inner.is_empty() {
            "".to_string()
        } else {
            format!("<div class='constraints'>{inner}</div>")
        };

        let tooltiptext = format!("<div class='tooltiptext'><div class='provers'>{options}</div>{constraints}<div class='type'>{typ}</div></div>");
        let tooltip = format!("<div class='tooltip'><span class='meta'>{varname}</span>{tooltiptext}</div>");
        return format!("<label><input type='radio' name='meta' id='{meta_id}' value='{meta_id}'>{tooltip}</label>")
    }

    /// Finds the head `DeBruijnIndex` in the `es` and creates a Meta with `bindings` and recursively converted arguments.
<<<<<<< HEAD
    pub fn to_body(&self, es: ES, bindings: S<Indexed<S<Bind>>>, owned_linked: Vec<S<Linked>>, polarity: Polarity) -> (Meta, HashSet<Var>) {
        let (head, var) = es.index_of(&self.head).expect(&format!("Undeclared variable: {}", self.head));
        let mut used = HashSet::new();
        let bind = var.bind.clone();
        if matches!(var.bind.borrow().polarity, Polarity::Goal) { used.insert(var); } // TODO consider reduction rules
        let mut args = Vec::new();
        for arg in self.args.iter() {
            let (arg, arg_used) = arg.to_term(&es, polarity);
            args.push(S::new(arg));
            used.extend(arg_used);
        }
 
        (Meta {
            assignment: Some(Assignment { head, args, bind, changes: Vec::new(), 
                _owned_linked: owned_linked, has_rigid_type: true, var_type: None, involved: Vec::new() }),
=======
    pub fn to_body(&self, es: ES, bindings: S<Bindings>, owned_linked: Vec<S<Linked>>, 
        position: &[Position], tokens: &mut Tokenization) -> Meta {
        let (head, decl) = es.index_of(&self.head).expect(&format!("Undeclared variable: {}", self.head));
        tokens.tokens.push((position.to_vec(), decl.clone()));
        let args = self.args.iter().enumerate().map(|(i, t)|
            t.to_expr(&es, &extend(position, &[Position::Arg(i)]), tokens, None)).collect();
 
        Meta {
            assignment: Some(Assignment { head, args, decl, changes: Vec::new(), _owned_linked: owned_linked, has_rigid_type: true, var_type: None }),
>>>>>>> upstream/main
            typ: None,
            gamma: es,
            constraints: Vec::new(),
            bindings: bindings.downgrade(),
            from_original_problem: true,
            _owned_bindings: Some(bindings),
            stats: SearchInfo::new_branch(),
            had_rigid_equation: false,
            branching: 1.0,
            parent: None,
            gamma_involved: Vec::new(),
            typ_involved: Vec::new(),
            dependence: 0
        }, used)
    }
}

<<<<<<< HEAD
impl IRTerm {
    /// Return a version of `es` with `self.lets` and `params`.
    pub fn extend_es(&self, es: &ES, owned_linked: &mut Vec<S<Linked>>, params: &[IRVar], polarity: Polarity) -> (ES, S<Indexed<S<Bind>>>, Entry) {
        let mut bindings = S::new(Indexed {
            params: params.iter().map(|v| S::new(v.to_bind(polarity))).collect(),
            lets: self.lets.iter().map(|d| S::new(d.var.to_bind(polarity))).collect()
        });

        let entry = Entry { params_id: next_u64(), lets_id: next_u64(), subst: None, context: None };
        let node = Node { entry: entry.clone(), bindings: bindings.downgrade() };
        let es = es.append(node, owned_linked);
=======
impl IRExpr {
    /// Extend `es` with fresh `Decl`s for `self.params` and `self.lets`, without compiling equations.
    pub fn add_local(&self, es: &ES, owned_linked: &mut Vec<S<Linked>>, 
        position: &[Position]) -> (ES, S<Bindings>) {
        let bindings = S::new(Bindings {
            params: self.params.iter().enumerate().map(|(i, d)| 
                S::new(d.to_decl(extend(position, &[Position::Param(i)])))).collect(),
            lets: self.lets.iter().enumerate().map(|(i, d)| 
                S::new(d.to_decl(extend(position, &[Position::Let(i)])))).collect()
        });

        let node = Node {
            entry: Entry { params_id: next_u64(), lets_id: next_u64(), subst: None, context: None },
            bindings: bindings.downgrade()
        };
        (es.append(node, owned_linked), bindings)
    }
>>>>>>> upstream/main

    /// Convert to the codomain `Meta`, translating each declaration in the extended ES.
    pub fn to_expr(&self, es: &ES, position: &[Position], tokens: &mut Tokenization, polarity: Option<Polarity>) -> S<Meta> {
        let mut owned_linked = Vec::new();
        let (es, mut bindings) = self.add_local(es, &mut owned_linked, position);

        for i in 0..self.params.len() {
            let decl = &mut bindings.borrow_mut().params[i];
            let position = extend(position, &[Position::Param(i)]);
            self.params[i].translate::<false>(decl, &es, &mut owned_linked, &position, tokens, polarity.map(Polarity::opposite));
        }
<<<<<<< HEAD
        (es, bindings, entry)
    }

    pub fn to_term(&self, es: &ES, polarity: Polarity) -> (Meta, HashSet<Var>) {
        let mut owned_linked = Vec::new();
        let (es, bindings, entry) = self.extend_es(es, &mut owned_linked, &self.params, polarity.opposite());
        let (mvar, mut used) = self.spine.to_body(es, bindings, owned_linked, polarity);
        used.retain(|v| v.entry_id != entry.params_id && v.entry_id != entry.lets_id); // TODO reduction rules
        (mvar, used)
    }

    pub fn from_lambda<const RULES: bool>(term: Term, bindings: W<Indexed<S<Bind>>>, html: bool) -> IRTerm {
        let mut owned_linked = Vec::new();
        let params = bindings.borrow().params.iter().map(|b| IRVar { name: b.borrow().name.clone() }).collect();
        let lets = bindings.borrow().lets.iter().map(|b| 
            IRLet { var: IRVar { name: b.borrow().name.clone() }, rules: Vec::new() }).collect();
        let goal_rules = term.base.borrow().typ.as_ref().map(|typ| get_rules(&typ.codomain())).unwrap_or_default();
        // TODO special WHNF that does not get stuck and does not unfold definitions
        IRTerm { params, lets, spine: IRSpine::from_body::<RULES>(term.whnf::<RULES, ()>(&mut owned_linked, &mut ()), html), goal_rules }
    }
}

fn bucket(indices: Vec<DeBruijnIndex>, len: usize) -> Vec<Vec<usize>> {
    let mut buckets = vec![Vec::new(); len];
    for DeBruijnIndex(DeBruijn(d), index) in indices {
        if let Param(index) = index {
            buckets[d as usize].push(index);
        }
    }
    buckets
}

impl IRType {
    pub fn to_type(&self, es: &ES, polarity: Polarity) -> (TypeBase, HashSet<Var>) {
        let mut owned_linked = Vec::new();
        let (codomain_es, bindings, entry) = self.codomain.extend_es(es, &mut owned_linked, &self.codomain.params, polarity.opposite());
        let (codomain, mut used) = self.codomain.spine.to_body(codomain_es.clone(), bindings, owned_linked, polarity);
        
        // let (codomain, mut used) = self.codomain.to_term(es, polarity);  

        let mut vars_used = HashSet::new();
        let params : Vec<Option<S<TypeBase>>> = self.params.iter().map(|t| 
            t.as_ref().map(|t| {
                let (param_type, param_used) = t.to_type(&codomain_es, polarity.opposite());
                vars_used.extend(param_used);
                S::new(param_type)
            })).collect();
        let lets : Vec<Option<S<TypeBase>>> = self.lets.iter().map(|t| 
            t.as_ref().map(|t| {
                let (let_type, let_used) = t.to_type(&codomain_es, polarity.opposite());
                vars_used.extend(let_used);
                S::new(let_type)
            })).collect();

        // Using `es` also ensures the top level is not mentioned. 
        let dbs = codomain_es.iter().filter_map(|(db, _, var)| if used.contains(&var) { Some(db) } else { None } ).collect();
        let vars_dbs = codomain_es.iter().filter_map(|(db, _, var)| if vars_used.contains(&var) { Some(db) } else { None } ).collect();
            
        used.extend(vars_used);
        used.retain(|v| v.entry_id != entry.params_id && v.entry_id != entry.lets_id); 

        (TypeBase {
            codomain_mvars: bucket(dbs,codomain_es.length()),
            types_mvars: bucket(vars_dbs, codomain_es.length()),

            codomain: S::new(codomain),
            types: S::new(Indexed { params, lets })
        }, used)
=======
        for i in 0..self.lets.len() {
            let decl = &mut bindings.borrow_mut().lets[i];
            let position = extend(position, &[Position::Let(i)]);
            self.lets[i].translate::<true>(decl, &es, &mut owned_linked, &position, tokens, polarity.map(Polarity::opposite));
        }

        S::new(self.spine.to_body(es, bindings, owned_linked, position, tokens))
    }

    pub fn from_lambda<const RULES: bool>(term: Term, bindings: W<Bindings>, html: bool) -> IRExpr {
        let mut owned_linked = Vec::new();
        let params = bindings.borrow().params.iter().map(|b|
            IRDecl { name: b.borrow().name.clone(), typ: None, equations: Vec::new() }).collect();
        let lets = bindings.borrow().lets.iter().map(|b|
            IRDecl { name: b.borrow().name.clone(), typ: None, equations: Vec::new() }).collect();
        let goal_rules = term.base.borrow().typ.as_ref().map(|typ| get_rules(&typ.codomain())).unwrap_or_default();
        // TODO special WHNF that does not get stuck and does not unfold definitions
        IRExpr { params, lets, spine: IRSpine::from_body::<RULES>(term.whnf::<RULES, ()>(&mut owned_linked, &mut (), false), html), goal_rules }
>>>>>>> upstream/main
    }
}

impl fmt::Display for IRSpine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;
        for t in &self.args {
            if t.params.is_empty() && t.lets.is_empty() && t.spine.args.is_empty() {
                write!(f, " {}", t)?;
            } else {
                write!(f, " ({})", t)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for IRExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.params.is_empty() || !self.lets.is_empty() {
            write!(f, "λ")?;
            for v in &self.params {
                write!(f, " {}", v.name)?;
            }
            for d in &self.lets {
                write!(f, ", {} := {:?}", d.name, d.equations)?;
            }
            write!(f, " ↦ ")?;
        }
        write!(f, "{}", self.spine)
    }
}

/// Displays an `IRExpr` as a Π-type rather than a λ-term.
pub struct AsType<'a>(pub &'a IRExpr);

impl fmt::Display for AsType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt_type(f, "\n")
    }
}

impl IRExpr {
    fn fmt_type(&self, f: &mut fmt::Formatter, sep: &str) -> fmt::Result {
        for d in &self.params {
            write!(f, "({} : ", d.name)?;
            match &d.typ {
                Some(t) => t.fmt_type(f, " ")?,
                None => write!(f, "*")?
            }
            write!(f, ") →{}", sep)?;
        }

        for d in &self.lets {
            write!(f, "({} : ", d.name)?;
            match &d.typ {
                Some(t) => t.fmt_type(f, " ")?,
                None => write!(f, "*")?
            }
            write!(f, " := {:?}) →{}", d.equations, sep)?;
        }

        write!(f, "{}", self.spine)
    }
}

impl IRDecl {
    /// Save this `IRDecl` as JSON to `file`.
    pub fn save(&self, file: String) {
        let file = File::create(file).unwrap();
        serde_json::to_writer(file, self).unwrap();
    }

    /// Load an `IRDecl` from a JSON `file`.
    pub fn load(file: String) -> IRDecl {
        let file = File::open(file).unwrap();
        serde_json::from_reader(file).unwrap()
    }
}

impl fmt::Debug for IREquation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ↦ {}", self.lhs, self.rhs)
    }
}