use crate::stats::*;

/// Smoothly transitions between `prior` and `a / b` as `b` increases to `breakpoint`.
pub fn div(a: f64, b: f64, prior: f64, breakpoint: f64) -> f64 {
    if b < breakpoint / 2.0 { return prior }
    if b > breakpoint { return a / b }
    let amount = 2.0 * b / breakpoint - 1.0;
    return prior * (1.0 - amount) + (a / b) * amount;
}

impl MetaInfo {
    /// The entropy of an unassigned metavariable.
    pub fn difficulty(&self) -> f64 {
        if self.has_rigid_equation { return 1.0 }
        
        // stats consists of only non-rigid while search_stats contains both.
        let prob_non_rigid = div(self.current_stats.attempts as f64, self.future_stats.attempts as f64, 1.0, 100.0);
        let steps_per_completion = div(self.current_stats.steps as f64, self.current_stats.completed_count as f64, 5.0, 100.0);

        // We take the weighted average of 1 and the average number of steps per completion, 
        // weighted by the probability that this metavariable obtains a rigid equation.
        ((1.0 - prob_non_rigid) + prob_non_rigid*steps_per_completion).clamp(1.0, 1000.0)
    }
}

impl AssignmentInfo {
    /// Weight between the children of a DFS node.
    pub fn weight(&self) -> f64 {
        1.0
    }
}