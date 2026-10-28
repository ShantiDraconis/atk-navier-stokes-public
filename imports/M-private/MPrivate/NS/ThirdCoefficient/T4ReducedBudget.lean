import Mathlib
import MPrivate.NS.ThirdCoefficient.ScaleInvariantBudget
import MPrivate.NS.ThirdCoefficient.T3ReducedSignedRoute

namespace MPrivate.NS.ThirdCoefficient

/-!
# T4ReducedBudget

This file contains the CONDITIONAL two-component T4 algebra.  It is admissible
only after the low coefficient has been independently eliminated by a valid
low-frequency estimate.  The rejected reverse-Poincare low-pass argument on
`ℝ³` is not such a certificate.

If low elimination is certified, T4c reduces to the two independent budgets

  integral aCross <= BC(u0)
  integral aAlign <= BA(u0).

Otherwise the three-component `ScaleInvariantBudget` route remains the source
of truth and an independent low budget is still required.

Audit identity rule: `aCross` and `aAlign` used here must be exactly the
coefficients already appearing in the certified T3 decomposition for the same
solution, cutoff, viscosity and time interval.  Scaling-equivalent proxies,
profile surrogates, finite-shell approximants and post-G1 reconstructed
quantities are not interchangeable with those coefficients.
-/

variable (I : (ℝ → ℝ) → ℝ → ℝ)

/-- Subadditivity assembles the two remaining component budgets, conditional on
using the already-defined reduced coefficient.  This theorem does not certify
low elimination. -/
theorem two_component_budget_assembles
    (hsub : IntegralSubadditive I)
    (aCross aAlign : ℝ → ℝ)
    (T BC BA : ℝ)
    (hC : ComponentBudget I aCross T BC)
    (hA : ComponentBudget I aAlign T BA) :
    I (reducedA3 aCross aAlign) T ≤ BC + BA := by
  unfold reducedA3
  have h := hsub aCross aAlign T
  unfold ComponentBudget at hC hA
  linarith

/-- Sum of two scale-invariant budget values is scale invariant. -/
theorem two_budget_values_scale_invariant
    {State : Type*}
    (scale : ℝ → State → State)
    (BC BA : State → ℝ)
    (hC : ScaleInvariantBudgetValue scale BC)
    (hA : ScaleInvariantBudgetValue scale BA) :
    ScaleInvariantBudgetValue scale (fun u => BC u + BA u) := by
  intro u lambda hlambda
  change BC (scale lambda u) + BA (scale lambda u) = BC u + BA u
  rw [hC u lambda hlambda, hA u lambda hlambda]

/-- Gate deciding whether the reduced two-component budget is even admissible. -/
structure ReducedT4Admissibility where
  actual_solution_class_identified : Prop
  low_elimination_certified : Prop
  low_elimination_valid_on_domain : Prop
  low_elimination_derived_from_actual_NS : Prop
  low_elimination_targets_same_low_block_as_T3 : Prop
  low_elimination_uses_same_cutoff_as_T3 : Prop
  low_elimination_uses_same_solution_and_interval : Prop
  no_reverse_low_pass_poincare : Prop
  strict_viscosity_margin_preserved : Prop
  same_viscosity_as_enstrophy_balance : Prop
  low_elimination_target_independent : Prop
  low_elimination_uniform_in_time : Prop
  no_hidden_regularization_gain : Prop
  no_post_G1_reconstruction_used_upstream : Prop

/-- Explicit reduced T4c frontier. These fields are obligations, not assumptions
silently imported into a final theorem. -/
structure ReducedT4cFrontier where
  admissible : ReducedT4Admissibility
  maximal_lifetime_is_actual_solution_lifetime : Prop
  maximal_lifetime_positive : Prop
  cross_coefficient_is_actual_cross_coefficient : Prop
  alignment_coefficient_is_actual_alignment_coefficient : Prop
  cross_coefficient_is_same_one_used_in_T3 : Prop
  alignment_coefficient_is_same_one_used_in_T3 : Prop
  no_proxy_substitution_for_cross_coefficient : Prop
  no_proxy_substitution_for_alignment_coefficient : Prop
  no_scaling_identity_counted_as_component_budget : Prop
  no_finite_shell_bound_counted_as_component_budget_without_limit_identity : Prop
  cross_budget_derived_from_actual_NS : Prop
  alignment_budget_derived_from_actual_NS : Prop
  cross_L1_budget : Prop
  alignment_L1_budget : Prop
  cross_nonnegative : Prop
  alignment_nonnegative : Prop
  cross_time_measurable : Prop
  alignment_time_measurable : Prop
  cross_budget_uniform_for_T_lt_Tstar : Prop
  alignment_budget_uniform_for_T_lt_Tstar : Prop
  common_Tstar_and_solution_interval : Prop
  same_solution_as_T3_decomposition : Prop
  same_cutoff_as_T3_decomposition : Prop
  same_viscosity_as_T3_decomposition : Prop
  same_concrete_integral_used_for_components : Prop
  same_time_measure_used_for_components : Prop
  passage_to_maximal_interval_justified : Prop
  cross_budget_scale_invariant : Prop
  alignment_budget_scale_invariant : Prop
  cross_budget_initial_data_only : Prop
  alignment_budget_initial_data_only : Prop
  constants_uniform_below_Tstar : Prop
  no_hidden_time_length_factor : Prop
  no_maximal_time_value : Prop
  cross_no_supY : Prop
  alignment_no_supY : Prop
  cross_no_Z_div_Y : Prop
  alignment_no_Z_div_Y : Prop
  cross_no_BKM_LPS : Prop
  alignment_no_BKM_LPS : Prop
  cross_no_future_critical_norm : Prop
  alignment_no_future_critical_norm : Prop
  cross_no_endpoint_reuse : Prop
  alignment_no_endpoint_reuse : Prop
  cross_no_higher_derivative : Prop
  alignment_no_higher_derivative : Prop
  cutoff_positive : Prop
  cutoff_prior_data_only : Prop
  cutoff_scale_covariant : Prop
  cutoff_independent_of_future_solution : Prop

end MPrivate.NS.ThirdCoefficient
