import Mathlib
import MPrivate.NS.ThirdCoefficient.ActualBonyToCrossT3
import MPrivate.NS.ThirdCoefficient.EightTermSignedGrouping
import MPrivate.NS.ThirdCoefficient.ActualCrossBudget

namespace MPrivate.NS.ThirdCoefficient

open Filter

/-!
# SignedSpacetimeCrossGain

This file isolates admissible routes from the actual cross block used in
`ActualBonyToCrossT3` to the integrated cross-energy gain.

Nothing here claims the missing PDE estimate.  The scalar identities in
`EightTermSignedGrouping` show that cancellation is algebraically possible, but
that fact alone does not imply a quantitative spacetime gain.  A second
reduction isolates a heat-semigroup part and a nonlinear Duhamel part of the
same low-velocity amplitude.
-/

variable (I : (ℝ → ℝ) → ℝ → ℝ)

/-- Abstract signed finite truncation of the actual mixed cross block. -/
def SignedCrossTruncation
    (crossPartial : ℕ → ℝ → ℝ)
    (aCross : ℝ → ℝ) : Prop :=
  ∀ t, Tendsto (fun N => crossPartial N t) atTop (nhds (aCross t))

/-- Uniform integrated gain at every finite truncation.  The same concrete
energy-dissipation density `g` is used for every truncation; only the signed
cross approximation varies with `N`. -/
def UniformSignedTruncationGain
    (crossPartial : ℕ → ℝ → ℝ)
    (g : ℝ → ℝ)
    (Cstar Tstar : ℝ) : Prop :=
  0 ≤ Cstar ∧
  ∀ N T, 0 ≤ T → T < Tstar →
    I (crossPartial N) T ≤ Cstar * I g T

/-- Exact limit-passage interface.  Pointwise convergence of the signed shell
truncations is not, by itself, enough for an arbitrary abstract integral `I`.
This proposition isolates the additional dominated-convergence/Fatou/uniform-
integrability input needed to pass the uniform upper bound to the same T3 cross
coefficient. -/
def SignedIntegralLimitPassage
    (crossPartial : ℕ → ℝ → ℝ)
    (aCross g : ℝ → ℝ)
    (Cstar Tstar : ℝ) : Prop :=
  SignedCrossTruncation crossPartial aCross →
  ∀ T, 0 ≤ T → T < Tstar →
    (∀ N, I (crossPartial N) T ≤ Cstar * I g T) →
    I aCross T ≤ Cstar * I g T

/-- Uniform signed finite-truncation gain plus a justified limit passage gives
exactly the integrated cross-energy gain required by `ActualCrossBudget`.
No pointwise low-pass reverse Poincare estimate appears. -/
theorem integrated_gain_of_uniform_signed_truncations
    (crossPartial : ℕ → ℝ → ℝ)
    (aCross g : ℝ → ℝ)
    (Cstar Tstar : ℝ)
    (hconv : SignedCrossTruncation crossPartial aCross)
    (htrunc : UniformSignedTruncationGain I crossPartial g Cstar Tstar)
    (hpass : SignedIntegralLimitPassage I crossPartial aCross g Cstar Tstar) :
    IntegratedCrossEnergyGain I aCross g Cstar Tstar := by
  rcases htrunc with ⟨hC, htrunc⟩
  refine ⟨hC, ?_⟩
  intro T hT hTstar
  exact hpass hconv T hT hTstar (fun N => htrunc N T hT hTstar)

/-- Exact heat/Duhamel decomposition of the same low-velocity amplitude used by
T3.  This is an identity requirement, not a change of coefficient. -/
def HeatDuhamelLowVelocitySplit
    (UL Uheat Uduhamel : ℝ → ℝ) : Prop :=
  ∀ t, UL t = Uheat t + Uduhamel t

/-- Elementary square splitting used after the exact heat/Duhamel identity. -/
theorem square_of_heat_duhamel_split
    (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  nlinarith

/-- Separate spacetime budgets for the linear heat part and the nonlinear
Duhamel part control the integral of the *same* low-velocity square coefficient
appearing in T3.  The theorem is pure integral bookkeeping; proving either
budget from ActualNS is a separate analytic task. -/
theorem low_velocity_square_budget_from_heat_duhamel
    (hmono : IntegralMonotone I)
    (hmul : IntegralConstMul I)
    (hadd : IntegralSubadditive I)
    (UL Uheat Uduhamel : ℝ → ℝ)
    (T Bheat Bduhamel : ℝ)
    (hsplit : HeatDuhamelLowVelocitySplit UL Uheat Uduhamel)
    (hheat : I (fun t => Uheat t ^ 2) T ≤ Bheat)
    (hduhamel : I (fun t => Uduhamel t ^ 2) T ≤ Bduhamel) :
    I (fun t => UL t ^ 2) T ≤ 2 * (Bheat + Bduhamel) := by
  have hpoint : ∀ t,
      UL t ^ 2 ≤ 2 * (Uheat t ^ 2 + Uduhamel t ^ 2) := by
    intro t
    rw [hsplit t]
    exact square_of_heat_duhamel_split (Uheat t) (Uduhamel t)
  have h1 :
      I (fun t => UL t ^ 2) T ≤
        I (fun t => 2 * (Uheat t ^ 2 + Uduhamel t ^ 2)) T :=
    hmono (fun t => UL t ^ 2)
      (fun t => 2 * (Uheat t ^ 2 + Uduhamel t ^ 2)) T hpoint
  have htwo : 0 ≤ (2 : ℝ) := by norm_num
  rw [hmul 2 (fun t => Uheat t ^ 2 + Uduhamel t ^ 2) T htwo] at h1
  have hsum :
      I (fun t => Uheat t ^ 2 + Uduhamel t ^ 2) T ≤
        Bheat + Bduhamel := by
    exact (hadd (fun t => Uheat t ^ 2) (fun t => Uduhamel t ^ 2) T).trans
      (add_le_add hheat hduhamel)
  exact h1.trans (mul_le_mul_of_nonneg_left hsum htwo)

/-- Audit frontier for the heat/Duhamel route.  The linear heat estimate and,
especially, the nonlinear Duhamel estimate must target the same low projection
and remain uniform below the actual maximal lifespan. -/
structure HeatDuhamelCrossFrontier where
  actual_solution_class_identified : Prop
  maximal_lifetime_is_actual_solution_lifetime : Prop
  maximal_lifetime_positive : Prop
  same_low_velocity_as_T3 : Prop
  exact_mild_solution_identity : Prop
  heat_term_is_low_projected_initial_semigroup : Prop
  duhamel_term_is_low_projected_nonlinearity : Prop
  same_viscosity_in_heat_kernel_and_NS : Prop
  heat_square_spacetime_budget_from_initial_data : Prop
  heat_budget_uniform_for_every_T_below_Tstar : Prop
  duhamel_square_spacetime_budget_from_actual_NS : Prop
  duhamel_budget_uniform_for_every_T_below_Tstar : Prop
  bony_paraproduct_remainder_inventory_complete : Prop
  signed_cancellation_preserved_in_duhamel_estimate : Prop
  cutoff_positive : Prop
  cutoff_initial_data_only : Prop
  cutoff_scale_covariant : Prop
  cutoff_independent_of_future_solution : Prop
  zero_frequency_handled : Prop
  no_hidden_time_length_factor : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_future_critical_norm : Prop
  no_maximal_time_value : Prop
  no_endpoint_reuse : Prop
  no_uncontrolled_higher_derivative : Prop
  no_post_G1_reconstruction_used_upstream : Prop

/-- The PDE-level obligations required before signed shell cancellation may be
used to certify the same cross coefficient appearing in T3. -/
structure SignedSpacetimeCrossFrontier where
  actual_solution_class_identified : Prop
  maximal_lifetime_is_actual_solution_lifetime : Prop
  maximal_lifetime_positive : Prop
  same_solution_as_T3_cross_block : Prop
  same_cross_coefficient_as_ActualBonyToCrossT3 : Prop
  actual_mixed_signed_block_identified : Prop
  finite_shell_truncations_defined : Prop
  finite_truncations_preserve_signs : Prop
  no_triangle_inequality_before_signed_grouping : Prop
  opposite_sign_shell_interactions_quantified : Prop
  cancellation_estimate_derived_from_actual_NS : Prop
  truncation_gain_uniform_in_shell_cutoff : Prop
  truncation_gain_uniform_for_every_T_below_Tstar : Prop
  truncation_limit_exists : Prop
  pointwise_truncation_limit_is_same_T3_cross_coefficient : Prop
  dominated_or_uniform_integrability_input_identified : Prop
  passage_limit_under_time_integral_justified : Prop
  limit_recovers_same_aCross_used_in_T3 : Prop
  zero_frequency_handled : Prop
  cutoff_positive : Prop
  cutoff_initial_data_only : Prop
  cutoff_scale_covariant : Prop
  cutoff_independent_of_future_solution : Prop
  coefficient_measurable : Prop
  dissipation_density_is_actual_grad_u_sq : Prop
  dissipation_density_measurable : Prop
  dissipation_density_nonnegative : Prop
  same_viscosity_as_energy_and_enstrophy_balance : Prop
  energy_budget_uniform_for_every_T_below_Tstar : Prop
  passage_to_maximal_interval_justified : Prop
  multiplier_initial_data_only : Prop
  multiplier_finite : Prop
  multiplier_scale_compatible : Prop
  no_hidden_time_length_factor : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_future_critical_norm : Prop
  no_maximal_time_value : Prop
  no_endpoint_reuse : Prop
  no_uncontrolled_higher_derivative : Prop
  no_post_G1_reconstruction_used_upstream : Prop

/-- If the signed-shell analysis has already produced the *same* integrated
cross gain as required by `ActualCrossBudget`, the existing budget theorem is
reused without changing the T3 coefficient.  This is composition only. -/
theorem signed_integrated_gain_closes_cross_budget
    (aCross g : ℝ → ℝ)
    (Cstar Tstar E0 nu : ℝ)
    (hgain : IntegratedCrossEnergyGain I aCross g Cstar Tstar)
    (henergy : UniformEnergyBudgetBelow I g Tstar E0 nu) :
    UniformCrossBudgetBelow I aCross Tstar
      (Cstar * (E0 / (2 * nu))) :=
  uniform_cross_budget_from_integrated_energy_gain
    I aCross g Cstar Tstar E0 nu hgain henergy

end MPrivate.NS.ThirdCoefficient
