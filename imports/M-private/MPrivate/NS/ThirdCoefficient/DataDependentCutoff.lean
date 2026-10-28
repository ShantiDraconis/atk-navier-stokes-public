import Mathlib
import MPrivate.NS.ThirdCoefficient.Specification
import MPrivate.NS.ThirdCoefficient.LowFrequencyScaleCovariance

namespace MPrivate.NS.ThirdCoefficient

/-!
# DataDependentCutoff

A cutoff used in the ThirdCoefficient route must transform with the data.
This file certifies only the scaling algebra.  It does not assert that an
appropriate cutoff exists for every Navier--Stokes datum.
-/

variable {State : Type*}

/-- A cutoff rule has NS frequency degree `+1`. -/
def CutoffRuleCovariant
    (scale : ℝ → State → State)
    (R : State → ℝ) : Prop :=
  ∀ u lambda, 0 < lambda → R (scale lambda u) = lambda * R u

/-- A scalar datum functional is scale invariant. -/
def BudgetInvariant
    (scale : ℝ → State → State)
    (B : State → ℝ) : Prop :=
  ∀ u lambda, 0 < lambda → B (scale lambda u) = B u

/-- Low-frequency coefficient generated from a covariant cutoff and an invariant
amplitude factor. -/
def lowCoefficient
    (R B : State → ℝ) (u : State) : ℝ :=
  (R u)^2 * B u

/-- Scaling certificate: degree `+1` cutoff plus degree `0` amplitude produces
degree `+2` coefficient, exactly the ThirdCoefficient scaling. -/
theorem lowCoefficient_critical_scaling
    (scale : ℝ → State → State)
    (R B : State → ℝ)
    (hR : CutoffRuleCovariant scale R)
    (hB : BudgetInvariant scale B) :
    ∀ u lambda, 0 < lambda →
      lowCoefficient R B (scale lambda u) =
        lambda^2 * lowCoefficient R B u := by
  intro u lambda hlambda
  unfold lowCoefficient
  rw [hR u lambda hlambda, hB u lambda hlambda]
  ring

/-- Nonnegativity is inherited from a nonnegative amplitude functional. -/
theorem lowCoefficient_nonneg
    (R B : State → ℝ)
    (hB : ∀ u, 0 ≤ B u) :
    ∀ u, 0 ≤ lowCoefficient R B u := by
  intro u
  unfold lowCoefficient
  exact mul_nonneg (sq_nonneg (R u)) (hB u)

/-- Scaling-level admissibility only.  This definition must not be interpreted as
sufficient for T3/T4: it says nothing about future dependence or integrability. -/
def AdmissibleLowCutoff
    (scale : ℝ → State → State)
    (R B : State → ℝ) : Prop :=
  CutoffRuleCovariant scale R ∧
  BudgetInvariant scale B ∧
  (∀ u, 0 ≤ R u) ∧
  (∀ u, 0 ≤ B u)

/-- Additional audit obligations required before a data-dependent cutoff can be
used in the actual Navier--Stokes route. -/
structure CutoffAuditFrontier
    (scale : ℝ → State → State)
    (R B : State → ℝ) where
  scaling_admissible : AdmissibleLowCutoff scale R B
  constructed_from_initial_data_only : Prop
  finite_on_admissible_data : Prop
  positive_when_denominators_require_it : Prop
  independent_of_Tstar : Prop
  independent_of_future_solution_values : Prop
  independent_of_future_critical_norm : Prop
  independent_of_supY : Prop
  independent_of_Z_div_Y : Prop
  independent_of_endpoint_criterion : Prop
  same_cutoff_used_across_low_cross_reconstruction : Prop
  cutoff_measurability_if_state_varies : Prop
  coefficient_integrability_not_inferred_from_scaling_alone : Prop

end MPrivate.NS.ThirdCoefficient
