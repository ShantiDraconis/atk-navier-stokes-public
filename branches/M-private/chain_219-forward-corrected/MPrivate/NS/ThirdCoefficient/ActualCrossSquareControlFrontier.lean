import Mathlib.Basic.Real.Basic

structure ActualCrossSquareControlFrontier where
  actual_cross_block_inventory_complete : Prop
  bony_representation : Prop
  holder_step : Prop
  factors_are_actual_norm_quantities : Prop
  high_derivative_factor_sq_le_Z : Prop
  low_vorticity_energy_le_Y : Prop
  low_velocity_identification : Prop
  projector_L2_bounded : Prop
  derivative_projector_commutation : Prop
  block_sum_uniform : Prop
  target_independent_constant : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_higher_derivative : Prop

theorem square_control_algebra
    (uLinf omegaL2 UL Y : ℝ)
    (hU : uLinf = UL)
    (hY : omegaL2 ^ 2 ≤ Y) :
    (uLinf * omegaL2) ^ 2 ≤ UL ^ 2 * Y := by
  rw [hU, mul_pow]
  exact mul_le_mul_of_nonneg_left hY (sq_nonneg UL)
