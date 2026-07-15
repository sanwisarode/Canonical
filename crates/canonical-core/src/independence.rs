use crate::core::*;
use crate::memory::*;
use crate::stats::MetaInfo;
use std::collections::HashMap;
use union_find::{UnionFind, UnionBySize, QuickUnionUf};

pub struct NextInfo {
    pub meta: W<Meta>,
    pub eligible: bool    
}

/// An independent component and the information used to choose its next metavariable.
pub struct SplitComponent {
    pub unassigned: Vec<NextInfo>,
    pub entropy: f64
}

/// The metavariables whose assignments may interact with `mvar`.
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

/// Collect the unassigned metavariables in the subtree of `meta` into `out`.
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

/// Partition the unassigned metavariables under `root` into independent components.
pub fn split(unassigned: Vec<W<Meta>>) -> Vec<SplitComponent> {
    let mut indices: HashMap<W<Meta>, usize> = HashMap::default();
    for (i, x) in unassigned.iter().enumerate() {
        indices.insert(x.clone(), i);
    }

    let mut involved_inverse: HashMap<W<Meta>, Vec<(W<Meta>, bool)>> = HashMap::new();
    for mvar in unassigned.iter() {
        for (i, codomain) in involved(mvar.clone()).into_iter() {
            if !involved_inverse.contains_key(&i) {
                involved_inverse.insert(i.clone(), Vec::new());
            }
            let arr = involved_inverse.get_mut(&i).unwrap();
            arr.push((mvar.clone(), codomain)); // TODO missing optimization if it's already at the last.
        }
    }

    let mut uf = QuickUnionUf::<UnionBySize>::new(unassigned.len());
    let mut eligible: Vec<bool> = vec![true; unassigned.len()];
    for (i, mvar) in unassigned.iter().enumerate() {
        let mut parent = Some(mvar);
        while let Some(p) = parent {
            if let Some(arr) = involved_inverse.get(p) {
                for (o, codomain) in arr {
                    uf.union(i, *indices.get(o).unwrap());
                    if *codomain {
                        eligible[indices[mvar]] = false;
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
        if let Some(slot) = slots[r] {
            buckets[slot].push(NextInfo { meta: mvar.clone(), eligible: eligible[indices[mvar]] });
        } else {
            slots[r] = Some(buckets.len());
            buckets.push(vec![NextInfo { meta: mvar.clone(), eligible: eligible[indices[mvar]] }])
        }
    }

    buckets.into_iter().map(|unassigned| {
        let entropy = unassigned.iter().map(|mvar|
            MetaInfo::new(mvar.meta.clone()).difficulty()
        ).product();
        SplitComponent { unassigned, entropy }
    }).collect()
}
