import Mathlib

namespace MPrivate.NS.PostG1

/-!
# G2HighFrequencyInterface

G2 begins only after G1-flex has produced the required a priori control.
Its job is to convert that analytic information into a fixed-scale control of
the high-frequency contribution to a recognized critical quantity.

No Littlewood--Paley theorem is asserted here. This is the exact interface that
a concrete kernel/LP proof must fill.  In particular, merely constructing a
`G2AnalyticObligations` value or selecting `G2Status.proved` is not evidence of
the analytic theorem.
-/

variable {State : Type*}

structure G2Data (State : Type*) where
  highCritical : State → ℝ → ℝ → ℝ
  cutoff : State → ℝ
  g1Control : State → ℝ
  initialDataBudget : State → ℝ

/-- Fixed-scale high-frequency critical control. -/
def FixedScaleHighCriticalControl
    (D : G2Data State) (u : State) (T M : ℝ) : Prop :=
  ∀ t, 0 ≤ t → t < T →
    D.highCritical u (D.cutoff u) t ≤ M

/-- The cutoff must be chosen independently of the unknown future critical norm. -/
def CutoffIndependentOfTarget
    (dependsOnFutureCriticalNorm : Bool) : Prop :=
  dependsOnFutureCriticalNorm = false

/-- Provenance requirements tying the abstract conclusion to actual G1 output
and initial data.  These fields prevent a numerically correct high-frequency
bound from being admitted with a circular or unrelated source. -/
structure G2ProvenanceObligations (D : G2Data State) where
  actual_solution_class_identified : Prop
  domain_identified : Prop
  same_solution_as_G1_output : Prop
  same_time_interval_as_G1_output : Prop
  maximal_lifetime_is_actual_solution_lifetime : Prop
  maximal_lifetime_positive : Prop
  same_viscosity_as_G1_output : Prop
  g1_output_used : Prop
  initial_data_budget_used : Prop
  cutoff_from_prior_data_only : Prop
  cutoff_independent_of_future_target : Prop
  constants_independent_of_Tstar : Prop
  constants_independent_of_truncation : Prop
  constants_uniform_below_Tstar : Prop
  no_maximal_time_value_used : Prop
  no_endpoint_reuse : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_future_critical_norm : Prop
  no_uncontrolled_higher_derivative : Prop

/-- G2 may use the output of G1 but may not assume the endpoint continuation
criterion it is supposed to help construct. -/
structure G2AnalyticObligations (D : G2Data State) where
  cutoff_positive : Prop
  cutoff_scale_covariant : Prop
  high_critical_nonnegative_or_norm_identified : Prop
  recognized_critical_space : Prop
  high_frequency_kernel_estimate : Prop
  projector_or_kernel_mapping_bound : Prop
  derivative_or_multiplier_commutation : Prop
  shell_sum_convergent : Prop
  shell_constant_uniform : Prop
  fixed_scale_uniformity : Prop
  uniform_for_every_T_below_Tstar : Prop
  passage_to_maximal_interval_justified : Prop
  time_measurability : Prop
  derived_from_G1_control : Prop
  provenance : G2ProvenanceObligations D
  no_future_critical_norm_in_cutoff : Prop
  no_endpoint_assumption : Prop
  no_hidden_higher_regularization : Prop
  conclusion_is_actual_high_critical_norm : Prop
  conclusion_high_critical_control : Prop

inductive G2Status where
  | notKernelProved
  | conditional
  | proved
  deriving DecidableEq, Repr

end MPrivate.NS.PostG1
