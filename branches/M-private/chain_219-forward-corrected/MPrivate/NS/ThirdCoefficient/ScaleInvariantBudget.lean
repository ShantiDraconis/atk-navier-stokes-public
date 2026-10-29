import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# ScaleInvariantBudget

Audit-safe bookkeeping for T4c.  This file proves only that separately certified
component budgets assemble.  It does not assert any Navier--Stokes time-integral
estimate.
-/

-- Abstract finite-time integral functional.
variable (I : (ℝ → ℝ) → ℝ → ℝ)

/-- Component budget statement on `[0,T]`. -/
def ComponentBudget
    (a : ℝ → ℝ) (T B : ℝ) : Prop :=
  I a T ≤ B

/-- Subadditivity property required from the concrete integral implementation. -/
def IntegralSubadditive : Prop :=
  ∀ a b T, I (fun t => a t + b t) T ≤ I a T + I b T

/-- Scale-invariant scalar budget under an abstract data scaling action. -/
def ScaleInvariantBudgetValue {State : Type*}
    (scale : ℝ → State → State)
    (B : State → ℝ) : Prop :=
  ∀ u lambda, 0 < lambda → B (scale lambda u) = B u

/-- Three component budgets assemble into a budget for their sum. -/
theorem three_component_budget_assembles
    (hsub : IntegralSubadditive I)
    (aLow aCross aAlign : ℝ → ℝ)
    (T BL BC BA : ℝ)
    (hL : ComponentBudget I aLow T BL)
    (hC : ComponentBudget I aCross T BC)
    (hA : ComponentBudget I aAlign T BA) :
    I (fun t => aLow t + aCross t + aAlign t) T ≤ BL + BC + BA := by
  have h1 := hsub (fun t => aLow t + aCross t) aAlign T
  have h2 := hsub aLow aCross T
  unfold ComponentBudget at hL hC hA
  linarith

/-- The combined budget remains scale invariant if each component budget value
is scale invariant. -/
theorem sum_budget_scale_invariant
    {State : Type*}
    (scale : ℝ → State → State)
    (BL BC BA : State → ℝ)
    (hL : ScaleInvariantBudgetValue scale BL)
    (hC : ScaleInvariantBudgetValue scale BC)
    (hA : ScaleInvariantBudgetValue scale BA) :
    ScaleInvariantBudgetValue scale (fun u => BL u + BC u + BA u) := by
  intro u lambda hlambda
  change BL (scale lambda u) + BC (scale lambda u) + BA (scale lambda u) =
    BL u + BC u + BA u
  rw [hL u lambda hlambda, hC u lambda hlambda, hA u lambda hlambda]

/-- Exact T4c frontier: all independently obtained component bounds are
required; none may be filled by a future critical norm, `sup Y`, `Z/Y`, or a
continuation criterion. The concrete integral and maximal-time passage must also
be certified. -/
structure T4cFrontier where
  coefficient_components_measurable : Prop
  coefficient_components_nonnegative : Prop
  concrete_integral_identified : Prop
  integral_subadditivity_certified : Prop
  low_budget : Prop
  cross_budget : Prop
  alignment_budget : Prop
  budgets_finite : Prop
  budgets_uniform_for_all_T_lt_Tstar : Prop
  maximal_time_passage_certified : Prop
  low_scale_invariant : Prop
  cross_scale_invariant : Prop
  alignment_scale_invariant : Prop
  budget_sum_scale_invariant : Prop
  budget_initial_data_only : Prop
  no_Tstar_dependence : Prop
  no_future_cutoff_dependence : Prop
  no_future_critical_norm : Prop
  no_supY : Prop
  no_ratio_by_Y : Prop
  no_continuation_criterion : Prop
  no_uncontrolled_higher_derivative : Prop
  no_global_conclusion_reuse : Prop

end MPrivate.NS.ThirdCoefficient
