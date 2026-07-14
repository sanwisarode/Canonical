use crate::core::*;
use crate::memory::*;
use crate::stats::MetaInfo;
use std::collections::HashMap;
use std::hash::{DefaultHasher, BuildHasherDefault};
use union_find::{UnionFind, UnionBySize, QuickUnionUf};

/// An independent component and the information used to choose its next metavariable.
pub struct SplitComponent {
    pub unassigned: Vec<W<Meta>>,
    pub eligible: Vec<bool>,
    pub entropy: f64
}

/// The metavariables whose assignments may interact with `mvar`.
pub fn involved(mvar: W<Meta>) -> Vec<W<Meta>> {
    let typ = mvar.borrow().typ.as_ref().unwrap();
    let mut result = typ.1.get_many(&typ.0.borrow().codomain_mvars);
    result.extend(mvar.borrow().gamma.involved());
    for constraint in &mvar.borrow().constraints {
        result.extend(constraint.involved())
    }
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
    let mut indices: HashMap<W<Meta>, usize, BuildHasherDefault<DefaultHasher>> = HashMap::default();
    for (i, x) in unassigned.iter().enumerate() {
        indices.insert(x.clone(), i);
    }

    let mut eligible = vec![true; unassigned.len()];
    let mut involved_inverse: HashMap<W<Meta>, Vec<W<Meta>>, BuildHasherDefault<DefaultHasher>> = HashMap::default();
    for (source_index, mvar) in unassigned.iter().enumerate() {
        let typ = mvar.borrow().typ.as_ref().unwrap();
        for target in typ.1.get_many(&typ.0.borrow().codomain_mvars) {
            if let Some(&target_index) = indices.get(&target) {
                if target_index != source_index {
                    eligible[target_index] = false;
                }
            }
        }
        for i in involved(mvar.clone()).iter() {
            if !involved_inverse.contains_key(&i) {
                involved_inverse.insert(i.clone(), Vec::new());
            }
            let arr = involved_inverse.get_mut(i).unwrap();
            if arr.last() != Some(mvar) {
                arr.push(mvar.clone());
            }
        }
    }

    let mut uf = QuickUnionUf::<UnionBySize>::new(unassigned.len());
    for (i, mvar) in unassigned.iter().enumerate() {
        let mut parent = Some(mvar);
        while let Some(p) = parent {
            if let Some(arr) = involved_inverse.get(p) {
                for o in arr {
                    uf.union(i, *indices.get(o).unwrap());
                }
            }
            parent = p.borrow().parent.as_ref().clone();
        }
    }

    let mut buckets: HashMap<usize, (Vec<W<Meta>>, Vec<bool>), BuildHasherDefault<DefaultHasher>> = HashMap::default();
    for (i, mvar) in unassigned.iter().enumerate() {
        let r = uf.find(i);
        let bucket = buckets.entry(r).or_default();
        bucket.0.push(mvar.clone());
        bucket.1.push(eligible[i]);
    }
    buckets.into_values().map(|(unassigned, eligible)| {
        let entropy = unassigned.iter().map(|mvar|
            MetaInfo::new(mvar.clone()).difficulty()
        ).product();
        SplitComponent { unassigned, eligible, entropy }
    }).collect()
}
