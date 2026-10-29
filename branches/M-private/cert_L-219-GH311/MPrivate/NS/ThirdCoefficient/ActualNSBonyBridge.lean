import Mathlib
import MPrivate.NS.ThirdCoefficient.ActualBonyToCrossT3

namespace MPrivate.NS.ThirdCoefficient.ActualNSBonyBridge

open MPrivate.NS.ThirdCoefficient
open MPrivate.NS.ThirdCoefficient.ActualBonyToCrossT3

/-!
# ActualNSBonyBridge

Audit-safe norm bridge for the actual Navier--Stokes Bony cross interaction.

The important correction is that the vorticity factor below is a projected
Littlewood--Paley block, not silently a low-frequency block.  Thus high blocks
may enter provided their L2 square function is controlled by the actual
enstrophy and the corresponding derivative square function by dissipation.
The PDE/LP construction itself remains an explicit analytic frontier.
-/

structure BonyCrossNormData where
  Vcross : ℝ
  x : ℝ
  b : ℝ
  Z : ℝ
  K : ℝ
  uL : ℝ
  wBlock : ℝ
  UL : ℝ
  Y : ℝ
  x_nonneg : 0 ≤ x
  b_nonneg : 0 ≤ b
  Z_nonneg : 0 ≤ Z
  K_nonneg : 0 ≤ K
  uL_nonneg : 0 ≤ uL
  wBlock_nonneg : 0 ≤ wBlock
  UL_nonneg : 0 ≤ UL
  Y_nonneg : 0 ≤ Y

/-- One-block certificate. `wBlock` may be low or high; no frequency relabeling
is permitted. -/
def BonyCrossNormCertified (d : BonyCrossNormData) : Prop :=
  d.Vcross ≤ d.x * d.b ∧
  d.x ^ 2 ≤ d.Z ∧
  d.b ^ 2 ≤ d.K ^ 2 * (d.uL * d.wBlock) ^ 2 ∧
  d.uL ^ 2 ≤ d.UL ^ 2 ∧
  d.wBlock ^ 2 ≤ d.Y

theorem certified_norm_data_gives_square_control
    (d : BonyCrossNormData)
    (h : BonyCrossNormCertified d) :
    CrossSquareControl d.b d.K d.UL d.Y := by
  exact crossSquareControl_of_bony_controls h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem certified_norm_data_gives_cross_T3
    (d : BonyCrossNormData)
    (eps : ℝ)
    (heps : 0 < eps)
    (h : BonyCrossNormCertified d) :
    d.Vcross ≤ eps * d.Z +
      (d.K ^ 2 / (4 * eps)) * crossCoefficientFromVelocity d.UL * d.Y := by
  exact crossT3_of_bony_controls
    heps h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- Square-function data for the shell-summed route.  These are scalar shadows
of the actual LP square functions; the theorem below only proves their final
Cauchy--Schwarz/Young algebra. -/
structure ProjectedShellAggregate where
  Vcross : ℝ
  UL : ℝ
  Y : ℝ
  Z : ℝ
  K : ℝ
  omegaSq : ℝ
  gradOmegaSq : ℝ
  omegaSq_nonneg : 0 ≤ omegaSq
  gradOmegaSq_nonneg : 0 ≤ gradOmegaSq
  Y_nonneg : 0 ≤ Y
  Z_nonneg : 0 ≤ Z
  K_nonneg : 0 ≤ K
  UL_nonneg : 0 ≤ UL
  shell_holder : Vcross ≤ K * UL * Real.sqrt omegaSq * Real.sqrt gradOmegaSq
  projected_vorticity_square_sum_le_Y : omegaSq ≤ Y
  projected_gradient_square_sum_le_Z : gradOmegaSq ≤ Z

/-- The shell-summed LP estimate gives the exact T3 shape without replacing a
high vorticity block by a low one. -/
theorem projected_shell_aggregate_gives_cross_T3
    (d : ProjectedShellAggregate)
    (eps : ℝ) (heps : 0 < eps) :
    d.Vcross ≤ eps * d.Z +
      (d.K ^ 2 / (4 * eps)) * crossCoefficientFromVelocity d.UL * d.Y := by
  have hsY : Real.sqrt d.omegaSq ≤ Real.sqrt d.Y :=
    Real.sqrt_le_sqrt d.projected_vorticity_square_sum_le_Y
  have hsZ : Real.sqrt d.gradOmegaSq ≤ Real.sqrt d.Z :=
    Real.sqrt_le_sqrt d.projected_gradient_square_sum_le_Z
  have hrootY : (Real.sqrt d.Y) ^ 2 = d.Y := Real.sq_sqrt d.Y_nonneg
  have hrootZ : (Real.sqrt d.Z) ^ 2 = d.Z := Real.sq_sqrt d.Z_nonneg
  have hprod :
      d.Vcross ≤ (Real.sqrt d.Z) * (d.K * d.UL * Real.sqrt d.Y) := by
    calc
      d.Vcross ≤ d.K * d.UL * Real.sqrt d.omegaSq * Real.sqrt d.gradOmegaSq := d.shell_holder
      _ ≤ d.K * d.UL * Real.sqrt d.Y * Real.sqrt d.Z := by
        have hKU : 0 ≤ d.K * d.UL := mul_nonneg d.K_nonneg d.UL_nonneg
        have h1 := mul_le_mul_of_nonneg_left hsY hKU
        have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg d.gradOmegaSq)
        have h3 := mul_le_mul_of_nonneg_left hsZ (mul_nonneg hKU (Real.sqrt_nonneg d.Y))
        exact le_trans h2 h3
      _ = (Real.sqrt d.Z) * (d.K * d.UL * Real.sqrt d.Y) := by ring
  have hyoung := young_product_absorption
    (Real.sqrt d.Z) (d.K * d.UL * Real.sqrt d.Y) eps heps
  calc
    d.Vcross ≤ (Real.sqrt d.Z) * (d.K * d.UL * Real.sqrt d.Y) := hprod
    _ ≤ eps * (Real.sqrt d.Z) ^ 2 +
        (d.K * d.UL * Real.sqrt d.Y) ^ 2 / (4 * eps) := hyoung
    _ = eps * d.Z +
        (d.K ^ 2 / (4 * eps)) * crossCoefficientFromVelocity d.UL * d.Y := by
      rw [hrootZ]
      have h_sqrt :
          (d.K * d.UL * Real.sqrt d.Y) ^ 2 =
            d.K ^ 2 * d.UL ^ 2 * d.Y := by
        calc
          (d.K * d.UL * Real.sqrt d.Y) ^ 2 =
              d.K ^ 2 * d.UL ^ 2 * (Real.sqrt d.Y ^ 2) := by ring
          _ = d.K ^ 2 * d.UL ^ 2 * d.Y := by rw [hrootY]
      rw [h_sqrt]
      have h_cross : crossCoefficientFromVelocity d.UL = d.UL ^ 2 := by rfl
      rw [h_cross]
      ring_nf

/-- Exact unresolved ActualNS-to-Bony obligations.  This is deliberately more
precise than the old low-vorticity proxy: every shell must preserve its actual
frequency identity and the sum must be controlled before Young is applied. -/
structure ActualNSBonyAnalyticFrontier where
  actual_NS_solution_class_pinned : Prop
  actual_domain_pinned : Prop
  actual_maximal_interval_pinned : Prop
  maximal_lifetime_positive : Prop
  actual_vorticity_and_strain_identified : Prop
  LP_projectors_constructed : Prop
  projector_mapping_bounds_in_required_norms : Prop
  derivative_projector_commutation_justified : Prop
  bony_identity_for_actual_nonlinearity : Prop
  all_cross_blocks_inventory_complete : Prop
  cross_block_partition_disjoint_or_overlap_accounted : Prop
  each_cross_block_preserves_actual_frequency_identity : Prop
  holder_bound_for_each_cross_block : Prop
  bernstein_or_localization_bound_valid : Prop
  assembled_cross_blocks_equal_actual_Vcross : Prop
  finite_truncation_identity_exact : Prop
  truncation_limit_recovers_actual_Vcross : Prop
  shell_sum_convergent : Prop
  shell_sum_limit_interchange_justified : Prop
  shell_sum_cauchy_schwarz_with_uniform_overlap : Prop
  projected_vorticity_L2_square_sum_le_Y : Prop
  projected_gradient_square_sum_le_Z : Prop
  low_velocity_square_le_UL_square : Prop
  commutator_remainders_controlled : Prop
  remainder_blocks_not_silently_dropped : Prop
  K_uniform_in_shells : Prop
  K_uniform_in_time : Prop
  K_independent_of_target_norm : Prop
  K_independent_of_Tstar_value : Prop
  same_cutoff_used_across_all_blocks : Prop
  cutoff_positive : Prop
  cutoff_scale_covariant : Prop
  cutoff_initial_data_only : Prop
  cutoff_independent_of_future_solution : Prop
  estimates_uniform_for_every_t_below_Tstar : Prop
  time_measurability : Prop
  operations_valid_for_pinned_solution_class : Prop
  no_hidden_regularization_gain : Prop
  no_frequency_relabeling : Prop
  no_shellwise_young_before_summation : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_endpoint_reuse : Prop
  no_future_critical_norm : Prop
  no_maximal_time_value : Prop
  no_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient.ActualNSBonyBridge
