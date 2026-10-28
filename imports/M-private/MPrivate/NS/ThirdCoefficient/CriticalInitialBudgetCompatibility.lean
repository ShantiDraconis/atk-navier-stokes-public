import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# CriticalInitialBudgetCompatibility

A T4c budget depending on a scale-invariant initial datum functional is not
ruled out by the energy-scaling no-go. This is only a homogeneity certificate:
it does not prove the required time-integral estimate.
-/

variable {State : Type*}

/-- Scale-invariant initial critical quantity. -/
def InitialCriticalInvariant
    (scale : ℝ → State → State)
    (Ncrit : State → ℝ) : Prop :=
  ∀ u lambda, 0 < lambda → Ncrit (scale lambda u) = Ncrit u

/-- Any scalar function of a scale-invariant quantity remains scale invariant. -/
theorem function_of_critical_invariant_is_invariant
    (scale : ℝ → State → State)
    (Ncrit : State → ℝ)
    (F : ℝ → ℝ)
    (hcrit : InitialCriticalInvariant scale Ncrit) :
    ∀ u lambda, 0 < lambda →
      F (Ncrit (scale lambda u)) = F (Ncrit u) := by
  intro u lambda hlambda
  rw [hcrit u lambda hlambda]

/-- Candidate critical budget value. -/
def criticalBudgetValue
    (Ncrit : State → ℝ) (F : ℝ → ℝ) (u : State) : ℝ :=
  F (Ncrit u)

/-- The candidate budget has degree zero whenever `Ncrit` is invariant. -/
theorem criticalBudgetValue_scale_invariant
    (scale : ℝ → State → State)
    (Ncrit : State → ℝ)
    (F : ℝ → ℝ)
    (hcrit : InitialCriticalInvariant scale Ncrit) :
    ∀ u lambda, 0 < lambda →
      criticalBudgetValue Ncrit F (scale lambda u) =
        criticalBudgetValue Ncrit F u := by
  intro u lambda hlambda
  unfold criticalBudgetValue
  rw [hcrit u lambda hlambda]

/-- Compatibility is deliberately weaker than the analytic T4 statement. -/
structure CriticalBudgetFrontier
    (scale : ℝ → State → State)
    (Ncrit : State → ℝ)
    (F : ℝ → ℝ) where
  critical_quantity_scale_invariant : InitialCriticalInvariant scale Ncrit
  critical_quantity_defined_on_admissible_initial_data : Prop
  critical_quantity_finite : Prop
  budget_function_finite_on_relevant_range : Prop
  budget_value_nonnegative : Prop
  budget_value_finite : Prop
  time_integral_coefficient_measurable : Prop
  time_integral_bounded_by_budget_for_each_T_lt_Tstar : Prop
  budget_uniform_in_T : Prop
  maximal_time_passage_certified : Prop
  budget_depends_only_on_initial_data : Prop
  no_Tstar_dependence : Prop
  no_future_cutoff_dependence : Prop
  no_future_critical_norm_dependence : Prop
  derived_without_supY : Prop
  derived_without_Z_div_Y : Prop
  derived_without_continuation_criterion : Prop
  derived_without_BKM_LPS : Prop
  derived_without_uncontrolled_higher_derivative : Prop
  derived_without_global_conclusion : Prop

/-- Audit status distinguishes mere scaling compatibility from an actual T4 proof. -/
inductive CriticalBudgetStatus where
  | scaleCompatibleOnly
  | analyticBudgetProved
  | refuted
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
