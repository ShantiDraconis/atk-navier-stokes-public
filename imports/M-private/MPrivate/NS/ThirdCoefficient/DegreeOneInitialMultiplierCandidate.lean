import Mathlib
import MPrivate.NS.ThirdCoefficient.DataDependentCutoff

namespace MPrivate.NS.ThirdCoefficient

/-!
# DegreeOneInitialMultiplierCandidate

Template for the multiplier required by the energy-budget T4 mechanism:

  Cstar(u0) = R(u0) * B(u0),

where `R` has frequency degree +1 and `B` is scale invariant.  Then `Cstar`
has degree +1 and `Cstar * E0` is scale invariant when `E0` has degree -1.

This is a scaling template only; no NSE pointwise estimate is asserted.
-/

variable {State : Type*}

/-- Candidate degree-one initial multiplier. -/
def initialMultiplier
    (R B : State → ℝ) (u : State) : ℝ :=
  R u * B u

/-- Covariant cutoff times invariant factor has degree +1. -/
theorem initialMultiplier_degree_one
    (scale : ℝ → State → State)
    (R B : State → ℝ)
    (hR : CutoffRuleCovariant scale R)
    (hB : BudgetInvariant scale B) :
    ∀ u lambda, 0 < lambda →
      initialMultiplier R B (scale lambda u) =
        lambda * initialMultiplier R B u := by
  intro u lambda hlambda
  unfold initialMultiplier
  rw [hR u lambda hlambda, hB u lambda hlambda]
  ring

/-- Nonnegative pieces give a nonnegative multiplier. -/
theorem initialMultiplier_nonnegative
    (R B : State → ℝ)
    (hR : ∀ u, 0 ≤ R u)
    (hB : ∀ u, 0 ≤ B u) :
    ∀ u, 0 ≤ initialMultiplier R B u := by
  intro u
  unfold initialMultiplier
  exact mul_nonneg (hR u) (hB u)

/-- Complete admissibility target for a degree-one initial multiplier. -/
structure InitialMultiplierFrontier
    (scale : ℝ → State → State)
    (R B : State → ℝ) where
  cutoff_covariant : CutoffRuleCovariant scale R
  invariant_factor : BudgetInvariant scale B
  cutoff_nonnegative : ∀ u, 0 ≤ R u
  invariant_factor_nonnegative : ∀ u, 0 ≤ B u
  finite_for_admissible_data : Prop
  independent_of_future_solution : Prop
  independent_of_L3_endpoint : Prop
  independent_of_sup_enstrophy : Prop
  independent_of_Z_div_Y : Prop

end MPrivate.NS.ThirdCoefficient
