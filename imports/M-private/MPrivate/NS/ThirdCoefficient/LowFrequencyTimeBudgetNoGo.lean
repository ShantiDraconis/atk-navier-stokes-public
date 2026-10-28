import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# LowFrequencyTimeBudgetNoGo

A positive time-constant low-frequency coefficient can be harmless for a local
T3 estimate, but it cannot have a uniform initial-data-only L1 budget on
arbitrarily long intervals.  This is a pure algebraic obstruction.
-/

/-- Model integral of a constant coefficient `c` over `[0,T]`. -/
def constantTimeBudget (c T : ℝ) : ℝ := c * T

/-- No finite scalar `B` can bound `c*T` for every nonnegative `T` when `c>0`. -/
theorem positive_constant_has_no_uniform_time_budget
    (c B : ℝ)
    (hc : 0 < c) :
    ¬ (∀ T : ℝ, 0 ≤ T → constantTimeBudget c T ≤ B) := by
  intro h
  let T : ℝ := max 0 (B / c + 1)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact le_max_left _ _
  have hbound := h T hT
  unfold constantTimeBudget at hbound
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hchoice : B / c + 1 ≤ T := by
    dsimp [T]
    exact le_max_right _ _
  have hmul : c * (B / c + 1) ≤ c * T := by
    exact mul_le_mul_of_nonneg_left hchoice (le_of_lt hc)
  have hident : c * (B / c + 1) = B + c := by
    field_simp [hc0]
  rw [hident] at hmul
  linarith

/-- Therefore a successful low-frequency T4c mechanism must contain more than
`aLow(t)=positive constant`: decay, finite support, cancellation/absorption, or
another independently integrable time-dependent mechanism is required. -/
def LowBudgetNeedsTimeMechanism (aLow : ℝ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ T : ℝ, 0 ≤ T → aLow T ≤ B

end MPrivate.NS.ThirdCoefficient
