import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
`scaleBy` is deliberately restricted to nonnegative integer spatial weights.
It is not a model for time scaling or negative weights such as kinetic energy.
Those conventions must be tracked separately in analytic bridges.
-/

/-- Spatial scaling weight for a quantity represented abstractly by a scalar. -/
def scaleBy (weight : ℕ) (lambda x : ℝ) : ℝ := lambda ^ weight * x

lemma linear_weight_squared (lambda x : ℝ) :
    (scaleBy 1 lambda x) ^ 2 = lambda ^ 2 * x ^ 2 := by
  simp [scaleBy, pow_two]
  ring

lemma quadratic_weight_times_linear (lambda a y : ℝ) :
    scaleBy 2 lambda a * scaleBy 1 lambda y = lambda ^ 3 * (a * y) := by
  simp [scaleBy]
  ring

lemma cubic_stretching_weight (lambda v : ℝ) :
    scaleBy 3 lambda v = lambda ^ 3 * v := by
  simp [scaleBy]

/-- If `‖∇u‖₃` has weight one, its square has the required coefficient weight two. -/
lemma gradL3_square_has_weight_two (lambda g : ℝ) :
    (lambda * g) ^ 2 = lambda ^ 2 * g ^ 2 := by
  ring

/-- The unsquared `L³` gradient/strain/vorticity norm has weight one, not two. -/
lemma unsquared_L3_weight_is_one (lambda g : ℝ) :
    lambda * g = scaleBy 1 lambda g := by
  simp [scaleBy]

/-- A coefficient with weight two times enstrophy with weight one has the same
    cubic weight as vortex stretching. -/
lemma critical_coefficient_matches_stretching (lambda a y : ℝ) :
    (lambda ^ 2 * a) * (lambda * y) = lambda ^ 3 * (a * y) := by
  ring

/-- Analytic scaling conventions that cannot be inferred from the scalar
positive-weight lemmas above. -/
structure ScalingConventionFrontier where
  scaling_parameter_positive : Prop
  spatial_dimension_is_three : Prop
  time_scales_with_lambda_squared : Prop
  velocity_has_degree_one : Prop
  vorticity_has_degree_two : Prop
  enstrophy_has_degree_one : Prop
  enstrophy_dissipation_has_degree_three : Prop
  stretching_has_degree_three : Prop
  third_coefficient_has_degree_two : Prop
  kinetic_energy_has_degree_minus_one : Prop
  viscosity_convention_fixed : Prop
  cutoff_scaling_convention_fixed : Prop
  no_mixing_fixed_and_scaled_cutoffs : Prop
  no_negative_weight_encoded_via_Nat_scaleBy : Prop

end MPrivate.NS.ThirdCoefficient
