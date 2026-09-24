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
pub struct Component {
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

fn involved_inverse(unassigned: &[W<Meta>]) -> HashMap<W<Meta>, Vec<(usize, bool)>> {
    let mut result: HashMap<W<Meta>, Vec<(usize, bool)>> = HashMap::new();
    for (i, mvar) in unassigned.iter().enumerate() {
        for (target, codomain) in involved(mvar.clone()).into_iter() {
            result.entry(target).or_default().push((i, codomain)); // TODO missing optimization if it's already at the last.
        }
    }
    result
}

/// Union metavariables whose assignments interact
fn partition(unassigned: &[W<Meta>],
             involved_inverse: &HashMap<W<Meta>, Vec<(usize, bool)>>) -> Vec<Vec<NextInfo>> {
    let mut uf = QuickUnionUf::<UnionBySize>::new(unassigned.len());
    let mut eligible: Vec<bool> = vec![true; unassigned.len()];
    for (i, mvar) in unassigned.iter().enumerate() {
        let mut parent = Some(mvar);
        while let Some(p) = parent {
            if let Some(arr) = involved_inverse.get(p) {
                for (o, codomain) in arr {
                    uf.union(i, *o);
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

fn entropy(infos: &[MetaInfo]) -> f64 {
    infos.iter().map(|info| info.difficulty()).product()
}

// Choose the metavariable to refine next in a component
fn select_next(component: &[NextInfo], infos: &[MetaInfo]) -> usize {
    let mut eligible = Vec::with_capacity(component.len());
    for (i, mvar) in component.iter().enumerate() {
        if infos[i].has_rigid_equation { return i }
        if mvar.eligible { eligible.push(i); }
    }

    let mut best = eligible.pop().expect("No eligible mvars!");
    for i in eligible.into_iter() {
        if infos[i].difficulty() > infos[best].difficulty() {
            best = i;
        }
    }
    best
}

// Partition the unassigned metavariables into independent components and choosing next mvar
pub fn split(unassigned: Vec<W<Meta>>) -> Vec<Component> {
    let involved_inverse = involved_inverse(&unassigned);
    let buckets = partition(&unassigned, &involved_inverse);

    buckets.into_iter().map(|component| {
        let mut infos: Vec<MetaInfo> = component.iter().map(|x| MetaInfo::new(x.meta.clone())).collect();
        let meta_entropy = entropy(&infos);
        let next_index = select_next(&component, &infos);
        let next = infos.swap_remove(next_index);

        let mut unassigned: Vec<W<Meta>> = component.into_iter().map(|x| x.meta).collect();
        // We use swap_remove for O(1) complexity since ordering does not matter anymore.
        unassigned.swap_remove(next_index);
        Component { next, unassigned, meta_entropy }
    }).collect()
}
