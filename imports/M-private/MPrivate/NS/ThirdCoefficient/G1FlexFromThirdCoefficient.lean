import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# G1FlexFromThirdCoefficient

Pure algebraic consequence of the exact enstrophy balance plus a successful
ThirdCoefficient T3 estimate. This file does not prove the Navier--Stokes
premises; it certifies the downstream implication once they are supplied.
-/

/-- Scalar form of the exact enstrophy balance

  (1/2) y' + nu Z = V.
-/
def EnstrophyBalance
    (yPrime nu Z V : ℝ) : Prop :=
  (1 / 2 : ℝ) * yPrime + nu * Z = V

/-- Flexible G1 signed stretching estimate. -/
def G1FlexEstimate
    (V theta nu Z a Y : ℝ) : Prop :=
  V ≤ theta * nu * Z + a * Y

/-- Exact differential inequality obtained from balance plus G1-flex. -/
theorem balance_and_G1flex_give_differential_inequality
    (yPrime nu Z V theta a Y : ℝ)
    (hbal : EnstrophyBalance yPrime nu Z V)
    (hg1 : G1FlexEstimate V theta nu Z a Y) :
    (1 / 2 : ℝ) * yPrime + (1 - theta) * nu * Z ≤ a * Y := by
  unfold EnstrophyBalance at hbal
  unfold G1FlexEstimate at hg1
  linarith

/-- If the surviving dissipation coefficient is nonnegative, dropping it gives
the scalar Gronwall precursor `(1/2)y' <= aY`. -/
theorem drop_nonnegative_dissipation
    (yPrime nu Z theta a Y : ℝ)
    (hineq : (1 / 2 : ℝ) * yPrime + (1 - theta) * nu * Z ≤ a * Y)
    (hnu : 0 ≤ nu)
    (hZ : 0 ≤ Z)
    (htheta : theta ≤ 1) :
    (1 / 2 : ℝ) * yPrime ≤ a * Y := by
  have hdiss : 0 ≤ (1 - theta) * nu * Z := by
    positivity
  linarith

/-- Strict G1-flex regime. -/
def StrictG1FlexParameters (theta nu : ℝ) : Prop :=
  0 ≤ theta ∧ theta < 1 ∧ 0 < nu

/-- With strict parameters and nonnegative Z, the surviving dissipative term is
nonnegative and has positive coefficient whenever Z is positive. -/
theorem strict_parameters_nonnegative_dissipation
    (theta nu Z : ℝ)
    (h : StrictG1FlexParameters theta nu)
    (hZ : 0 ≤ Z) :
    0 ≤ (1 - theta) * nu * Z := by
  rcases h with ⟨ht0, ht1, hnu⟩
  positivity

/-- What remains upstream of this algebraic closure.  The temporal fields are
explicit because finite-time estimates do not automatically give a uniform
bound on the maximal interval.  A record value is an obligation bundle, not a
proof that ActualNS satisfies it. -/
structure G1FlexAnalyticBridge where
  actual_solution_class_identified : Prop
  exact_enstrophy_balance_for_actual_NS : Prop
  signed_third_coefficient_estimate : Prop
  strict_theta_range : Prop
  positive_viscosity : Prop
  same_viscosity_used_in_balance_and_absorption : Prop
  dissipation_nonnegative : Prop
  coefficient_nonnegative : Prop
  coefficient_scale_critical : Prop
  coefficient_measurable : Prop
  coefficient_locally_integrable : Prop
  coefficient_L1_time_budget : Prop
  finite_time_budget_uniform_below_Tstar : Prop
  passage_to_maximal_interval : Prop
  budget_scale_invariant : Prop
  budget_initial_data_only : Prop
  budget_non_circular : Prop
  constants_uniform_below_Tstar : Prop
  no_hidden_time_length_factor : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_endpoint_value_assumed : Prop
  no_future_critical_norm : Prop
  no_maximal_time_value : Prop
  no_uncontrolled_higher_derivative : Prop
  no_global_conclusion_reuse : Prop
  regularization_removal_justified : Prop

end MPrivate.NS.ThirdCoefficient
