import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# CrossLowVelocityTimeBudgetNoGo

Suppose the only available estimate for a cross coefficient is a uniform-in-time
bound of the form

  aCross(t) <= C * R^3 * E0,

coming from low-frequency Bernstein plus the kinetic-energy bound. For a fixed
initial-data cutoff `R`, this yields at best a time-linear integral bound and
cannot provide a uniform T4 budget independent of the unknown lifespan.
-/

/-- Constant Bernstein-energy majorant. -/
def CrossBernsteinEnergyMajorant
    (C R E0 : ℝ) : ℝ :=
  C * R^3 * E0

/-- A positive constant majorant accumulates linearly in time. -/
def ConstantTimeIntegral (c T : ℝ) : ℝ := c * T

/-- For positive majorant, the abstract integrated upper bound is unbounded as
`T` grows. -/
theorem positive_cross_majorant_exceeds_any_fixed_budget
    (C R E0 B : ℝ)
    (hC : 0 < C)
    (hR : 0 < R)
    (hE : 0 < E0) :
    ∃ T : ℝ, 0 < T ∧
      B < ConstantTimeIntegral (CrossBernsteinEnergyMajorant C R E0) T := by
  let c := CrossBernsteinEnergyMajorant C R E0
  have hc : 0 < c := by
    dsimp [c, CrossBernsteinEnergyMajorant]
    positivity
  let T := max 1 ((B + 1) / c)
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left 1 ((B + 1) / c))
  refine ⟨T, hT, ?_⟩
  have hlower : (B + 1) / c ≤ T := le_max_right 1 ((B + 1) / c)
  have hc0 : 0 ≤ c := le_of_lt hc
  have hmul := mul_le_mul_of_nonneg_left hlower hc0
  dsimp [ConstantTimeIntegral]
  dsimp [c] at hc hmul ⊢
  have hcne : CrossBernsteinEnergyMajorant C R E0 ≠ 0 := ne_of_gt hc
  have hid : CrossBernsteinEnergyMajorant C R E0 * ((B + 1) / CrossBernsteinEnergyMajorant C R E0) = B + 1 := by
    field_simp [hcne]
  rw [hid] at hmul
  linarith

/-- Audit conclusion: Bernstein+energy alone cannot certify a lifespan-uniform
T4 bound for `aCross = ||u_L||_infinity^2` at fixed cutoff. -/
def CrossBernsteinEnergyT4Status : String :=
  "FORMAL_REFUTED_AS_UNIFORM_T4_MECHANISM_WITHOUT_SPACETIME_GAIN"

/-- What an admissible cross budget must add. -/
structure CrossSpacetimeGainFrontier where
  concrete_cross_coefficient_identified : Prop
  coefficient_nonnegative : Prop
  coefficient_measurable : Prop
  time_decay_or_integrability_gain : Prop
  gain_uniform_on_every_T_below_Tstar : Prop
  passage_to_maximal_interval_justified : Prop
  derived_from_actual_NS : Prop
  scale_invariant_total_budget : Prop
  initial_data_only : Prop
  cutoff_scale_covariant : Prop
  cutoff_independent_of_future_solution : Prop
  constants_uniform_in_cutoff_and_shells : Prop
  no_hidden_time_length_factor : Prop
  no_endpoint_reuse : Prop
  no_future_critical_norm : Prop
  no_maximal_time_value : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_uncontrolled_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient
