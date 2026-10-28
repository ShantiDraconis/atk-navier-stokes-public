import Mathlib
import MPrivate.NS.ThirdCoefficient.AlignmentDepletionInequality

namespace MPrivate.NS.ThirdCoefficient

/-!
# BarrierClassifierTests

Regression tests for the direction of the known-barrier comparison.
-/

/-- The zero coefficient must never be classified as dominating the positive
constant barrier `1`. -/
theorem zero_does_not_dominate_positive_barrier :
    ¬ DominatesKnownBarrier (fun _ : ℝ => 0) (fun _ : ℝ => 1) := by
  intro h
  rcases h with ⟨c, hc, hdom⟩
  have h0 := hdom 0
  norm_num at h0
  linarith

/-- By contrast, the old (incorrect) upper-bound direction would accept zero,
which is why it cannot be used as a rejection criterion. -/
theorem zero_has_trivial_upper_bound_by_positive_barrier :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, (0 : ℝ) ≤ C * 1 := by
  refine ⟨0, by norm_num, ?_⟩
  intro t
  norm_num

/-- A barrier dominates itself with positive constant one. -/
theorem barrier_dominates_itself
    (B : ℝ → ℝ) :
    DominatesKnownBarrier B B := by
  refine ⟨1, by norm_num, ?_⟩
  intro t
  simp

end MPrivate.NS.ThirdCoefficient
