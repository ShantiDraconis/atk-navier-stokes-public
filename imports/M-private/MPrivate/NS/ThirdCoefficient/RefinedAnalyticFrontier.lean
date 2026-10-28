import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# RefinedAnalyticFrontier

Minimal unresolved analytic frontier after current algebraic reductions,
scaling tests, circularity tests and no-go certificates.

All component frontiers below are subject to identity continuity: the low,
cross, alignment, dissipation and energy-budget objects must refer to the same
actual Navier--Stokes solution, maximal interval, viscosity, cutoff where
applicable, and concrete T3 coefficients.  Matching scaling or using a proxy is
not sufficient.
-/

inductive LowClosureMode where
  | directSignedAbsorptionWithExtraSpectralGap
  | integrableScaleCovariantProfile
  | positiveLowCoefficientWithIndependentBudget
  deriving DecidableEq, Repr

structure LowClosureFrontier where
  mode : LowClosureMode
  actualNS_pointwise_estimate : Prop
  same_low_block_as_T3 : Prop
  same_solution_and_interval_as_T3 : Prop
  same_viscosity_as_T3 : Prop
  same_cutoff_as_T3 : Prop
  extra_spectral_gap_if_direct : Prop
  shell_or_profile_representation_valid : Prop
  representation_recovers_same_low_object : Prop
  zero_frequency_handled : Prop
  shell_sum_or_profile_limit_justified : Prop
  constants_uniform : Prop
  no_false_reverse_lowpass_poincare : Prop
  scale_covariance : Prop
  nonnegative_coefficient_if_used : Prop
  measurable_coefficient_if_used : Prop
  L1_budget_if_coefficient_used : Prop
  budget_uses_same_concrete_time_integral : Prop
  budget_uniform_below_Tstar : Prop
  budget_initial_data_only : Prop
  scaling_not_counted_as_budget : Prop
  finite_shell_bound_not_counted_without_limit_identity : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_endpoint_reuse : Prop
  no_future_solution_cutoff : Prop

structure CrossClosureFrontier where
  exact_cross_block_inventory : Prop
  spectral_representation_from_actual_NS : Prop
  same_cross_block_as_T3 : Prop
  same_cross_coefficient_as_T3 : Prop
  same_UL_as_T3_low_Linfinity_factor : Prop
  same_solution_and_interval_as_T3 : Prop
  same_viscosity_as_T3 : Prop
  same_cutoff_as_T3 : Prop
  projector_and_commutator_control : Prop
  factor_nonnegative : Prop
  dissipative_factor_square_le_Z : Prop
  young_remainder_independent_factorization : Prop
  candidate_can_be_velocity_low_Linf_squared : Prop
  low_velocity_identification : Prop
  no_proxy_substitution_for_UL : Prop
  coefficient_degree_two : Prop
  coefficient_nonnegative : Prop
  coefficient_measurable : Prop
  L1_budget : Prop
  budget_uses_same_concrete_time_integral : Prop
  budget_uniform_below_Tstar : Prop
  budget_passage_to_maximal_interval : Prop
  budget_initial_data_only : Prop
  constants_target_independent : Prop
  no_scaling_only_identification : Prop
  no_Y_denominator : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_endpoint_reuse : Prop
  no_future_critical_norm : Prop

structure AlignmentClosureFrontier where
  joint_direction_strain_quantity_derived : Prop
  same_alignment_block_as_T3 : Prop
  same_alignment_coefficient_as_T3 : Prop
  same_solution_and_interval_as_T3 : Prop
  same_viscosity_as_T3 : Prop
  same_cutoff_as_T3 : Prop
  zero_sets_handled : Prop
  strain_amplitude_degree_two : Prop
  angular_defect_dimensionless : Prop
  angular_defect_bounded : Prop
  defect_measurable : Prop
  commutator_evolution : Prop
  transport_estimate : Prop
  near_far_principal_value_kernel_split : Prop
  exceptional_tail_control : Prop
  uniform_strict_absorption_margin : Prop
  epsilon_limit_lower_semicontinuity : Prop
  tightness_preserves_strict_margin : Prop
  effective_volume_normalisation_without_hidden_Linf : Prop
  signed_alignment_factorization : Prop
  no_proxy_substitution_for_alignment_quantity : Prop
  L1_defect_budget : Prop
  budget_uses_same_concrete_time_integral : Prop
  budget_uniform_below_Tstar : Prop
  budget_initial_data_only : Prop
  no_scaling_only_identification : Prop
  no_rho_star_Z_div_Y_loop : Prop
  no_Phi_L3_endpoint_loop : Prop
  no_hidden_endpoint_or_future_norm : Prop

structure DissipationClosureFrontier where
  viscosity_positive : Prop
  same_viscosity_as_actual_enstrophy_balance : Prop
  epsilon_good_nonnegative : Prop
  epsilon_low_nonnegative : Prop
  epsilon_cross_nonnegative : Prop
  epsilon_align_nonnegative : Prop
  total_strictly_below_viscosity : Prop
  strict_margin_uniform_in_regularization : Prop
  strict_margin_survives_limit : Prop

structure EnergyBudgetClosureFrontier where
  same_solution_and_interval_as_component_budget : Prop
  same_viscosity_as_energy_balance : Prop
  same_gradient_density_as_actual_energy_dissipation : Prop
  same_concrete_time_integral : Prop
  degree_one_initial_multiplier : Prop
  pointwise_a_le_multiplier_gradU2 : Prop
  initial_energy_budget : Prop
  multiplier_finite : Prop
  multiplier_initial_data_only : Prop
  multiplier_scale_covariant : Prop
  no_hidden_time_length_factor : Prop
  multiplier_no_endpoint_reuse : Prop
  multiplier_no_supY : Prop
  multiplier_no_Z_div_Y : Prop
  multiplier_no_future_critical_norm : Prop

structure G1FlexMinimalFrontier where
  actual_solution_class_identified : Prop
  exact_actualNS_enstrophy_balance : Prop
  valid_signed_spectral_decomposition : Prop
  spectral_to_evolution_cost_bridge : Prop
  low : LowClosureFrontier
  cross : CrossClosureFrontier
  alignment : AlignmentClosureFrontier
  dissipation : DissipationClosureFrontier
  all_components_same_actual_solution : Prop
  all_components_same_maximal_interval : Prop
  all_components_same_viscosity : Prop
  all_components_same_cutoff_where_applicable : Prop
  all_components_are_same_T3_objects : Prop
  combined_a3_degree_two : Prop
  combined_a3_nonnegative : Prop
  combined_a3_measurable : Prop
  combined_a3_L1 : Prop
  combined_budget_uses_same_concrete_integral : Prop
  finite_time_budget_uniform_below_Tstar : Prop
  passage_T_to_Tstar_justified : Prop
  combined_budget_scale_invariant : Prop
  budget_initial_data_only : Prop
  no_endpoint_value_assumed : Prop
  no_global_conclusion_reuse : Prop
  no_post_G1_result_used_upstream : Prop
  regularization_to_actualNS_passage : Prop

structure DirectPostG1Frontier where
  gronwall_from_integrable_a3 : Prop
  uniform_enstrophy_on_open_maximal_interval : Prop
  same_actual_solution_as_G1 : Prop
  same_maximal_interval_as_G1 : Prop
  same_viscosity_as_G1 : Prop
  energy_uniform_L2 : Prop
  grad_u_controlled_by_vorticity : Prop
  Sobolev_L6_from_grad : Prop
  interpolation_L2_L6_to_L3 : Prop
  pointwise_L3_bound : Prop
  essential_supremum_L3_bound : Prop
  actual_L3_norm_not_proxy : Prop
  solution_class_matches_endpoint_theorem : Prop
  domain_and_pressure_hypotheses_match : Prop
  maximal_interval_convention_matches : Prop
  exact_ESS_hypothesis_map : Prop
  external_theorem_statement_pinned : Prop
  external_reference_pinned : Prop
  external_endpoint_invocation : Prop
  exclude_finite_maximal_time : Prop
  downstream_of_G1_only : Prop
  not_used_to_establish_G1_or_T4 : Prop

structure LPPostG1Frontier where
  high_frequency_kernel_theorem : Prop
  fixed_scale_low_frequency_bound : Prop
  common_cutoff_reconstruction : Prop
  same_actual_solution_as_G1_G2 : Prop
  same_maximal_interval_as_G1_G2 : Prop
  same_viscosity_as_G1_G2 : Prop
  cutoff_independent_of_future_critical_norm : Prop
  pointwise_L3_bound : Prop
  essential_supremum_L3_bound : Prop
  actual_L3_norm_not_proxy : Prop
  exact_ESS_hypothesis_map : Prop
  external_reference_pinned : Prop
  downstream_of_G1_only : Prop
  not_used_to_establish_G1_or_T4 : Prop

inductive OverallNSStatus where
  | G1Open
  | G1ClosedEndpointPending
  | endpointMapped
  | globalRegularityEstablished
  deriving DecidableEq, Repr

/-- Current status remains conservative: the analytic `ActualNS -> G1-flex`
bridge is not yet certified. -/
def currentOverallNSStatus : OverallNSStatus := .G1Open

end MPrivate.NS.ThirdCoefficient
