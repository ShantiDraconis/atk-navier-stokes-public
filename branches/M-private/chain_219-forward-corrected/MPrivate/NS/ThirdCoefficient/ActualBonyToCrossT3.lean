import MPrivate.NS.ThirdCoefficient.ActualBonyLPConcrete
import MPrivate.NS.ThirdCoefficient.CrossVelocityFactorization

namespace MPrivate.NS.ThirdCoefficient.ActualBonyToCrossT3

open MPrivate.NS.ThirdCoefficient
open MPrivate.NS.ThirdCoefficient.ActualBonyLPConcrete

/-!
Pure composition layer from the concrete Bony/LP scalar controls to the already
verified cross-T3 algebra. No new PDE estimate is asserted here.

The algebra is valid only after an actual Navier--Stokes/Bony bridge supplies
the listed analytic inputs with constants uniform in time, truncation and the
unknown target norm.  In particular, this file does not identify the actual
cross blocks, does not prove the Littlewood--Paley estimates, and does not prove
any temporal T4 budget.
-/

/-- The concrete Bony/LP controls imply the generic square-control interface. -/
theorem crossSquareControl_of_bony_controls
    {b K uL wL UL Y : ℝ}
    (hBony : b ^ 2 ≤ K ^ 2 * (uL * wL) ^ 2)
    (hVel : uL ^ 2 ≤ UL ^ 2)
    (hLow : wL ^ 2 ≤ Y) :
    CrossSquareControl b K UL Y := by
  unfold CrossSquareControl
  exact bony_cross_bound_from_controls hBony hVel hLow

/-- Once the actual cross representation and dissipative factor are supplied,
all remaining algebra to the cross-T3 bound is closed. -/
theorem crossT3_of_bony_controls
    {Vcross x b Z K uL wL UL Y eps : ℝ}
    (heps : 0 < eps)
    (hV : Vcross ≤ x * b)
    (hx : x ^ 2 ≤ Z)
    (hBony : b ^ 2 ≤ K ^ 2 * (uL * wL) ^ 2)
    (hVel : uL ^ 2 ≤ UL ^ 2)
    (hLow : wL ^ 2 ≤ Y) :
    Vcross ≤ eps * Z +
      (K ^ 2 / (4 * eps)) * crossCoefficientFromVelocity UL * Y := by
  have hsq : CrossSquareControl b K UL Y :=
    crossSquareControl_of_bony_controls hBony hVel hLow
  exact cross_T3_with_velocity_square_coefficient
    Vcross x b Z K UL Y eps heps hV hx hsq

/-- Exact analytic obligations left after this composition layer.  This is a
register of gates, not evidence that any gate has been discharged. -/
structure AnalyticFrontier where
  actual_bony_decomposition : Prop
  actual_cross_block_inventory_complete : Prop
  chosen_block_matches_uL_wL_proxy : Prop
  actual_bony_holder_factor : Prop
  actual_cross_representation : Prop
  cross_representation_uses_nonnegative_norm_factors : Prop
  dissipative_factor_control : Prop
  dissipative_factor_survives_block_sum : Prop
  low_velocity_identification : Prop
  low_vorticity_energy_control : Prop
  projector_L2_bounded : Prop
  derivative_projector_commutation : Prop
  commutator_remainder_controlled : Prop
  finite_or_infinite_shell_sum_justified : Prop
  shell_constant_uniform : Prop
  target_independent_constant : Prop
  time_independent_constant : Prop
  truncation_independent_constant : Prop
  cutoff_positive : Prop
  cutoff_from_prior_data_only : Prop
  cutoff_scale_covariant : Prop
  time_measurability : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_endpoint_reuse : Prop
  no_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient.ActualBonyToCrossT3
