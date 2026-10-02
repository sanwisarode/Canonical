use crate::core::*;
use crate::memory::*;
use crate::stats::MetaInfo;
use rustc_hash::FxHashMap as HashMap;
use union_find::{UnionFind, UnionBySize, QuickUnionUf};

/// An independent component produced by split
pub struct Component {
    pub next: MetaInfo,
    pub unassigned: Vec<W<Meta>>,
    pub meta_entropy: f64,
}

// The metavariables whose assignments might interact with mvar
fn involved(mvar: &W<Meta>) -> impl Iterator<Item = W<Meta>> + '_ {
    let meta = mvar.borrow();
    meta.gamma_involved.iter().chain(&meta.typ_involved).cloned()
        .chain(meta.constraints.iter().flat_map(|constraint| constraint.involved()))
}

// Collect the unassigned metavariables in the subtree
pub fn collect_unassigned(meta: W<Meta>, out: &mut Vec<W<Meta>>) {
    match &meta.borrow().assignment {
        None => out.push(meta.clone()),
        Some(assignment) => {
            for arg in assignment.args.iter() {
                collect_unassigned(arg.downgrade(), out);
            }
        }
    }
}

fn involved_inverse(unassigned: &[W<Meta>]) -> HashMap<usize, Vec<usize>> {
    let mut result: HashMap<usize, Vec<usize>> = HashMap::default();
    for (i, mvar) in unassigned.iter().enumerate() {
        for target in involved(mvar) {
            result.entry(target.usize()).or_default().push(i); // TODO missing optimization if it's already at the last.
        }
    }
    result
}

fn entropy(infos: &[MetaInfo]) -> f64 {
    infos.iter().map(|info| info.difficulty()).product()
}

fn independent(mvar: &W<Meta>) -> bool {
    mvar.borrow().dependence == 0 && mvar.borrow().parent.as_ref().is_none_or(independent)
}

// Choose the metavariable to refine next in a component
fn select_next(component: &[W<Meta>], infos: &[MetaInfo]) -> usize {
    let mut eligible = Vec::with_capacity(component.len());
    for (i, mvar) in component.iter().enumerate() {
        if infos[i].has_rigid_equation { return i }
        if independent(mvar) { eligible.push(i) };
    }

    let mut best = eligible.pop().expect("No eligible mvars!");
    for i in eligible.into_iter() {
        if infos[i].difficulty() > infos[best].difficulty() {
            best = i;
        }
    }
    best
}


fn to_component(component: &Vec<W<Meta>>) -> Component {
    let mut infos: Vec<MetaInfo> = component.iter().map(|x| MetaInfo::new(x.clone())).collect();
    let meta_entropy = entropy(&infos);
    let next_index = select_next(&component, &infos);
    let next = infos.swap_remove(next_index);

    let mut unassigned: Vec<W<Meta>> = component.into_iter().map(|x| x.clone()).collect();
    // We use swap_remove for O(1) complexity since ordering does not matter anymore.
    unassigned.swap_remove(next_index);
    Component { next, unassigned, meta_entropy }
}

/// Union metavariables whose assignments interact
pub fn split(unassigned: &[W<Meta>]) -> Vec<Component> {
    let involved_inverse = involved_inverse(unassigned);
    let mut uf = QuickUnionUf::<UnionBySize>::new(unassigned.len());
    for (i, mvar) in unassigned.iter().enumerate() {
        let mut parent = Some(mvar);
        while let Some(p) = parent {
            if let Some(arr) = involved_inverse.get(&p.usize()) {
                for o in arr {
                    uf.union(i, *o);
                }
            }
            parent = p.borrow().parent.as_ref().clone();
        }
    }

    let mut buckets: Vec<Vec<W<Meta>>> = Vec::new();
    let mut slots: Vec<Option<usize>> = vec![None; unassigned.len()];
    for (i, mvar) in unassigned.iter().enumerate() {
        let r = uf.find(i);
        if let Some(slot) = slots[r] {
            buckets[slot].push(mvar.clone());
        } else {
            slots[r] = Some(buckets.len());
            buckets.push(vec![mvar.clone()]);
        }
    }
    buckets.iter().map(to_component).collect()
}