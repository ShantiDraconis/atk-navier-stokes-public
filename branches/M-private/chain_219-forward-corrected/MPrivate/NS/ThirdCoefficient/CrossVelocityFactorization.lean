import Mathlib
import MPrivate.NS.ThirdCoefficient.CrossTermYoungAbsorption
import MPrivate.NS.ThirdCoefficient.CrossCoefficientScalingCorrection

namespace MPrivate.NS.ThirdCoefficient

/-!
# CrossVelocityFactorization

Concrete algebraic reduction for the cross block.

If the Young factor `b` obeys

  b^2 <= K^2 * U_L^2 * Y,

then the Young remainder factors without dividing by `Y`:

  b^2/(4 eps) <= (K^2/(4 eps)) * U_L^2 * Y.

Thus `aCross = U_L^2` is a legitimate pointwise candidate at the algebraic
level. The PDE work is reduced to proving the square-control inequality and an
independent L1_t budget for `U_L^2`.
-/

/-- Square-control target for the actual cross interaction. -/
def CrossSquareControl
    (b K U Y : ℝ) : Prop :=
  b^2 ≤ K^2 * U^2 * Y

/-- Young remainder factors through `Y` with `aCross = U^2`. -/
theorem young_remainder_from_cross_square_control
    (b K U Y eps : ℝ)
    (heps : 0 < eps)
    (h : CrossSquareControl b K U Y) :
    b^2 / (4 * eps) ≤
      (K^2 / (4 * eps)) * crossCoefficientFromVelocity U * Y := by
  unfold CrossSquareControl at h
  unfold crossCoefficientFromVelocity
  have hden : 0 < 4 * eps := by positivity
  apply (div_le_iff₀ hden).2
  calc
    b^2 ≤ K^2 * U^2 * Y := h
    _ = (K^2 / (4 * eps)) * U^2 * Y * (4 * eps) := by
      field_simp [ne_of_gt heps]

/-- Combining the generic Young step with square control gives the cross T3
bound with no target-dependent denominator. -/
theorem cross_T3_with_velocity_square_coefficient
    (Vcross x b Z K U Y eps : ℝ)
    (heps : 0 < eps)
    (hV : Vcross ≤ x * b)
    (hx : x^2 ≤ Z)
    (hsq : CrossSquareControl b K U Y) :
    Vcross ≤ eps * Z +
      (K^2 / (4 * eps)) * crossCoefficientFromVelocity U * Y := by
  have hy := cross_absorbed_if_square_le_Z Vcross x b Z eps heps hV hx
  have hr := young_remainder_from_cross_square_control b K U Y eps heps hsq
  linarith

/-- Exact remaining analytic frontier for this candidate.
The pointwise algebra above is not a temporal T4 certificate by itself. -/
structure CrossVelocityAnalyticFrontier where
  actual_cross_representation_V_le_xb : Prop
  dissipative_factor_x_sq_le_Z : Prop
  square_control_b_sq_le_K_sq_UL_sq_Y : Prop
  K_independent_of_target : Prop
  K_uniform_in_time : Prop
  K_uniform_in_cutoff_and_shells : Prop
  low_velocity_Linf_degree_one : Prop
  low_velocity_measurable : Prop
  coefficient_nonnegative : Prop
  coefficient_measurable : Prop
  low_velocity_Linf_sq_L1_budget : Prop
  budget_uniform_for_every_T_below_Tstar : Prop
  passage_to_maximal_interval_justified : Prop
  budget_scale_invariant : Prop
  budget_initial_data_only : Prop
  cutoff_positive : Prop
  cutoff_scale_covariant : Prop
  cutoff_initial_data_only : Prop
  cutoff_independent_of_future_solution : Prop
  no_hidden_time_length_factor : Prop
  no_maximal_time_value : Prop
  no_future_critical_norm : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_endpoint_reuse : Prop
  no_uncontrolled_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient
