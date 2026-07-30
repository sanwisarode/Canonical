use crate::core::*;
use crate::memory::*;
use crate::stats::MetaInfo;
use std::collections::HashMap;
use union_find::{UnionFind, UnionBySize, QuickUnionUf};

pub struct NextInfo {
    pub meta: W<Meta>,
    pub eligible: bool
}

/// An independent component produced by split
pub struct Partition {
    pub next: MetaInfo,
    pub unassigned: Vec<W<Meta>>,
    pub meta_entropy: f64,
}

// The metavariables whose assignments might interact with mvar
fn involved(mvar: W<Meta>) -> Vec<(W<Meta>, bool)> {
    let typ = mvar.borrow().typ.as_ref().unwrap();
    let codomain: Vec<(W<Meta>, bool)> = typ.1.get_many(&typ.0.borrow().codomain_mvars).into_iter().map(|x| (x, true)).collect();
    let mut constraints = mvar.borrow().gamma.involved();
    for constraint in &mvar.borrow().constraints {
        constraints.extend(constraint.involved())
    }
    let mut result: Vec<(W<Meta>, bool)> = constraints.into_iter().map(|x| (x, false)).collect();
    result.extend(codomain);
    return result;
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

fn index_map(unassigned: &[W<Meta>]) -> HashMap<W<Meta>, usize> {
    let mut indices: HashMap<W<Meta>, usize> = HashMap::default();
    for (i, x) in unassigned.iter().enumerate() {
        indices.insert(x.clone(), i);
    }
    indices
}

fn involved_inverse(unassigned: &[W<Meta>]) -> HashMap<W<Meta>, Vec<(W<Meta>, bool)>> {
    let mut result: HashMap<W<Meta>, Vec<(W<Meta>, bool)>> = HashMap::new();
    for mvar in unassigned.iter() {
        for (i, codomain) in involved(mvar.clone()).into_iter() {
            if !result.contains_key(&i) {
                result.insert(i.clone(), Vec::new());
            }
            let arr = result.get_mut(&i).unwrap();
            arr.push((mvar.clone(), codomain)); // TODO missing optimization if it's already at the last.
        }
    }
    result
}

/// Union metavariables whose assignments interact
fn partition(unassigned: &[W<Meta>], indices: &HashMap<W<Meta>, usize>,
             involved_inverse: &HashMap<W<Meta>, Vec<(W<Meta>, bool)>>) -> Vec<Vec<NextInfo>> {
    let mut uf = QuickUnionUf::<UnionBySize>::new(unassigned.len());
    let mut eligible: Vec<bool> = vec![true; unassigned.len()];
    for (i, mvar) in unassigned.iter().enumerate() {
        let mut parent = Some(mvar);
        while let Some(p) = parent {
            if let Some(arr) = involved_inverse.get(p) {
                for (o, codomain) in arr {
                    uf.union(i, *indices.get(o).unwrap());
                    if *codomain {
                        eligible[i] = false;
                    }
                }
            }
            parent = p.borrow().parent.as_ref().clone();
        }
    }

    let mut buckets: Vec<Vec<NextInfo>> = Vec::new();
    let mut slots: Vec<Option<usize>> = vec![None; unassigned.len()];
    for (i, mvar) in unassigned.iter().enumerate() {
        let r = uf.find(i);
        let info = NextInfo { meta: mvar.clone(), eligible: eligible[i] };
        if let Some(slot) = slots[r] {
            buckets[slot].push(info);
        } else {
            slots[r] = Some(buckets.len());
            buckets.push(vec![info]);
        }
    }
    buckets
}

fn entropy(component: &[NextInfo]) -> f64 {
    component.iter().map(|mvar| MetaInfo::new(mvar.meta.clone()).difficulty()).product()
}

// Choose the metavariable to refine next in a component
fn select_next(component: &[NextInfo]) -> (MetaInfo, usize) {
    let mut infos = Vec::with_capacity(component.len());
    for (i, mvar) in component.iter().enumerate() {
        let info = MetaInfo::new(mvar.meta.clone());
        let has_rigid_equation = info.has_rigid_equation;
        let next = (info, i);
        if has_rigid_equation { return next }
        if mvar.eligible { infos.push(next); }
    }

    let mut best = infos.pop().expect("No eligible mvars!");
    for info in infos.into_iter() {
        if info.0.difficulty() > best.0.difficulty() {
            best = info;
        }
    }
    best
}

// Partition the unassigned metavariables into independent components and choosing next mvar
pub fn split(unassigned: Vec<W<Meta>>) -> Vec<Partition> {
    let indices = index_map(&unassigned);
    let involved_inverse = involved_inverse(&unassigned);
    let buckets = partition(&unassigned, &indices, &involved_inverse);

    buckets.into_iter().map(|component| {
        let meta_entropy = entropy(&component);
        let (next, next_index) = select_next(&component);

        let mut unassigned: Vec<W<Meta>> = component.into_iter().map(|x| x.meta).collect();
        // We use swap_remove for O(1) complexity since ordering does not matter anymore.
        unassigned.swap_remove(next_index);
        Partition { next, unassigned, meta_entropy }
    }).collect()
}
