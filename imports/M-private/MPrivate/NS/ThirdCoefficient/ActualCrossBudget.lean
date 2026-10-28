import Mathlib
import MPrivate.NS.ThirdCoefficient.EnergyBudgetMultiplier
import MPrivate.NS.ThirdCoefficient.EnergyMultiplierScaling
import MPrivate.NS.ThirdCoefficient.ScaleInvariantBudget
import MPrivate.NS.ThirdCoefficient.CrossLowVelocityTimeBudgetNoGo

namespace MPrivate.NS.ThirdCoefficient

/-!
# ActualCrossBudget

Audit-safe closure of the bookkeeping part of the cross T4 budget.

Three routes are separated explicitly:

1. a direct pointwise multiplier route `aCross(t) <= Cstar * g(t)`;
2. a weaker integrated route `I aCross T <= Cstar * I g T`;
3. a coefficient-factor route

     aCross(t) = cLow(t) * g(t),
     0 <= cLow(t) <= Cstar.

The third route is admissible only if that factorization is proved for the SAME
cross coefficient already produced by the certified T3/Bony route.  It may not
be introduced by redefining `aCross`, since the existing T3 coefficient is
proportional to the low-velocity square.  Thus this file never replaces the
analytic problem by a different coefficient.

The algebra below does not manufacture the genuinely open PDE input: either a
uniform initial-data-only bound on an actually identified coefficient factor
must be derived from ActualNS, or the integrated gain must be proved directly.
-/

variable (I : (ℝ → ℝ) → ℝ → ℝ)

/-- Uniform cross budget on every finite interval below a candidate maximal
lifetime. The budget value is independent of `T`. -/
def UniformCrossBudgetBelow
    (aCross : ℝ → ℝ) (Tstar BC : ℝ) : Prop :=
  ∀ T, 0 ≤ T → T < Tstar → I aCross T ≤ BC

/-- Uniform kinetic-energy budget on every finite interval below `Tstar`. -/
def UniformEnergyBudgetBelow
    (g : ℝ → ℝ) (Tstar E0 nu : ℝ) : Prop :=
  ∀ T, 0 ≤ T → T < Tstar → EnergyIntegralBudget I g T E0 nu

/-- Pointwise spacetime gain. -/
def CrossSpacetimeEnergyGain
    (aCross g : ℝ → ℝ) (Cstar : ℝ) : Prop :=
  EnergyMultiplierPointwise aCross g Cstar

/-- Direct integrated gain. This is the exact interface needed when the PDE
argument controls the cross coefficient only after time integration. -/
def IntegratedCrossEnergyGain
    (aCross g : ℝ → ℝ) (Cstar Tstar : ℝ) : Prop :=
  0 ≤ Cstar ∧
  ∀ T, 0 ≤ T → T < Tstar → I aCross T ≤ Cstar * I g T

/-- A time-dependent coefficient bounded uniformly by an initial-data-only
constant. The PDE proof of such a bound is deliberately not encoded here. -/
def UniformCrossCoefficientBound
    (cLow : ℝ → ℝ) (Cstar : ℝ) : Prop :=
  0 ≤ Cstar ∧ ∀ t, 0 ≤ cLow t ∧ cLow t ≤ Cstar

/-- Optional low-velocity square route. This is retained as a sufficient
mechanism but is not required by the coefficient or integrated routes. -/
def LowVelocitySquareEnergyGain
    (UL g : ℝ → ℝ) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ t, UL t ^ 2 ≤ B * g t

/-- Audit obligations required specifically for any claim of
`LowVelocitySquareEnergyGain`. -/
structure LowVelocitySquareGainFrontier where
  low_velocity_is_actual_low_projection : Prop
  dissipation_density_is_actual_energy_dissipation : Prop
  gain_derived_from_actual_NS : Prop
  gain_scale_compatible : Prop
  multiplier_initial_data_only : Prop
  multiplier_degree_one : Prop
  multiplier_finite : Prop
  multiplier_uniform_in_time : Prop
  cutoff_positive : Prop
  cutoff_scale_covariant : Prop
  cutoff_initial_data_only : Prop
  no_generic_reverse_lowpass_poincare : Prop
  extra_spectral_gap_explicit_if_used : Prop
  cancellation_or_mean_zero_explicit_if_used : Prop
  no_hidden_zero_frequency_loss : Prop
  no_future_critical_norm : Prop
  no_endpoint_reuse : Prop
  no_BKM_LPS : Prop
  no_supY : Prop
  no_Z_div_Y : Prop

/-- If `A` is scale invariant and `B` has degree one, then the concrete
multiplier `A*B` has degree one. -/
theorem invariant_factor_times_degree_one_multiplier
    (A B Bscaled lambda : ℝ)
    (hB : DegreeOneMultiplier B Bscaled lambda) :
    DegreeOneMultiplier (A * B) (A * Bscaled) lambda := by
  unfold DegreeOneMultiplier at hB ⊢
  rw [hB]
  ring

/-- A bounded nonnegative coefficient multiplying the nonnegative dissipation
density gives the exact pointwise multiplier estimate needed by the existing
energy-budget theorem. -/
theorem cross_spacetime_gain_from_uniform_coefficient
    (aCross cLow g : ℝ → ℝ)
    (Cstar : ℝ)
    (hcoef : ∀ t, aCross t = cLow t * g t)
    (hbound : UniformCrossCoefficientBound cLow Cstar)
    (hg : ∀ t, 0 ≤ g t) :
    CrossSpacetimeEnergyGain aCross g Cstar := by
  rcases hbound with ⟨hC, hbound⟩
  refine ⟨hC, ?_⟩
  intro t
  rw [hcoef t]
  exact mul_le_mul_of_nonneg_right (hbound t).2 (hg t)

/-- Optional pointwise route from a low-velocity square gain. -/
theorem cross_spacetime_gain_from_low_velocity_square
    (aCross UL g : ℝ → ℝ)
    (A B : ℝ)
    (hA : 0 ≤ A)
    (hcoef : ∀ t, aCross t = A * UL t ^ 2)
    (hUL : LowVelocitySquareEnergyGain UL g B) :
    CrossSpacetimeEnergyGain aCross g (A * B) := by
  rcases hUL with ⟨hB, hUL⟩
  refine ⟨mul_nonneg hA hB, ?_⟩
  intro t
  rw [hcoef t]
  calc
    A * UL t ^ 2 ≤ A * (B * g t) :=
      mul_le_mul_of_nonneg_left (hUL t) hA
    _ = (A * B) * g t := by ring

/-- Pointwise gain plus the kinetic-energy budget gives a uniform cross budget. -/
theorem uniform_cross_budget_from_energy_gain
    (hmono : IntegralMonotone I)
    (hmul : IntegralConstMul I)
    (aCross g : ℝ → ℝ)
    (Cstar Tstar E0 nu : ℝ)
    (hgain : CrossSpacetimeEnergyGain aCross g Cstar)
    (henergy : UniformEnergyBudgetBelow I g Tstar E0 nu) :
    UniformCrossBudgetBelow I aCross Tstar
      (Cstar * (E0 / (2 * nu))) := by
  intro T hT hTstar
  exact energy_multiplier_closes_component_budget
    I hmono hmul aCross g Cstar T E0 nu hgain
    (henergy T hT hTstar)

/-- Integrated gain is already enough. No pointwise comparison between
`aCross` and `g` is used in this theorem. -/
theorem uniform_cross_budget_from_integrated_energy_gain
    (aCross g : ℝ → ℝ)
    (Cstar Tstar E0 nu : ℝ)
    (hgain : IntegratedCrossEnergyGain I aCross g Cstar Tstar)
    (henergy : UniformEnergyBudgetBelow I g Tstar E0 nu) :
    UniformCrossBudgetBelow I aCross Tstar
      (Cstar * (E0 / (2 * nu))) := by
  intro T hT hTstar
  rcases hgain with ⟨hC, hgain⟩
  have hcross : I aCross T ≤ Cstar * I g T := hgain T hT hTstar
  rcases henergy T hT hTstar with ⟨hnu, hE0, hbudget⟩
  exact hcross.trans (mul_le_mul_of_nonneg_left hbudget hC)

/-- Uniform coefficient control gives the complete cross budget once the energy
budget is supplied. This route is valid only after the factorization is proved
for the already-certified T3 cross coefficient. -/
theorem uniform_cross_budget_from_uniform_coefficient
    (hmono : IntegralMonotone I)
    (hmul : IntegralConstMul I)
    (aCross cLow g : ℝ → ℝ)
    (Cstar Tstar E0 nu : ℝ)
    (hcoef : ∀ t, aCross t = cLow t * g t)
    (hbound : UniformCrossCoefficientBound cLow Cstar)
    (hg : ∀ t, 0 ≤ g t)
    (henergy : UniformEnergyBudgetBelow I g Tstar E0 nu) :
    UniformCrossBudgetBelow I aCross Tstar
      (Cstar * (E0 / (2 * nu))) := by
  exact uniform_cross_budget_from_energy_gain
    I hmono hmul aCross g Cstar Tstar E0 nu
    (cross_spacetime_gain_from_uniform_coefficient aCross cLow g Cstar hcoef hbound hg)
    henergy

/-- Full bookkeeping chain for the optional pointwise low-velocity route. -/
theorem uniform_cross_budget_from_low_velocity_square_gain
    (hmono : IntegralMonotone I)
    (hmul : IntegralConstMul I)
    (aCross UL g : ℝ → ℝ)
    (A B Tstar E0 nu : ℝ)
    (hA : 0 ≤ A)
    (hcoef : ∀ t, aCross t = A * UL t ^ 2)
    (hUL : LowVelocitySquareEnergyGain UL g B)
    (henergy : UniformEnergyBudgetBelow I g Tstar E0 nu) :
    UniformCrossBudgetBelow I aCross Tstar
      ((A * B) * (E0 / (2 * nu))) := by
  exact uniform_cross_budget_from_energy_gain
    I hmono hmul aCross g (A * B) Tstar E0 nu
    (cross_spacetime_gain_from_low_velocity_square aCross UL g A B hA hcoef hUL)
    henergy

/-- Squared low-velocity amplitudes are pointwise nonnegative. -/
theorem low_velocity_square_nonnegative
    (UL : ℝ → ℝ) :
    ∀ t, 0 ≤ UL t ^ 2 := by
  intro t
  exact sq_nonneg (UL t)

/-- The unresolved analytic content needed for an ActualNS cross-budget
certificate. Either the uniform-coefficient route or a direct integrated route
may be used; neither is counted merely because the interface exists. -/
structure ActualCrossBudgetFrontier where
  actual_solution_class_identified : Prop
  maximal_lifetime_is_actual_solution_lifetime : Prop
  maximal_lifetime_positive : Prop
  actual_cross_coefficient_identified : Prop
  factorization_targets_same_cross_coefficient_as_T3 : Prop
  factorization_derived_not_defined_ad_hoc : Prop
  actual_cross_factorization_as_coefficient_times_dissipation : Prop
  actual_cross_coefficient_bound_from_actual_NS : Prop
  coefficient_bound_initial_data_only : Prop
  coefficient_bound_uniform_below_Tstar : Prop
  coefficient_bound_scale_compatible : Prop
  coefficient_measurable : Prop
  coefficient_nonnegative : Prop
  kinetic_energy_density_identified : Prop
  kinetic_energy_density_measurable : Prop
  kinetic_energy_density_nonnegative : Prop
  direct_integrated_cross_energy_gain_from_actual_NS : Prop
  integrated_gain_uniform_for_every_T_below_Tstar : Prop
  integrated_gain_uses_same_concrete_integral : Prop
  integrated_gain_uses_same_solution_and_interval : Prop
  integrated_gain_targets_same_cross_coefficient_as_T3 : Prop
  optional_pointwise_gain_from_actual_NS : Prop
  multiplier_nonnegative : Prop
  multiplier_finite : Prop
  multiplier_degree_one : Prop
  multiplier_initial_data_only : Prop
  energy_budget_uniform_below_Tstar : Prop
  energy_budget_uses_same_solution_and_interval : Prop
  passage_to_maximal_interval_justified : Prop
  budget_scale_invariant : Prop
  same_viscosity_as_enstrophy_balance : Prop
  cutoff_scale_covariant : Prop
  cutoff_independent_of_future_solution : Prop
  constants_uniform_in_cutoff_and_shells : Prop
  no_hidden_time_length_factor : Prop
  no_generic_reverse_lowpass_poincare : Prop
  no_hidden_zero_frequency_loss : Prop
  no_post_G1_reconstruction_used_upstream : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_future_critical_norm : Prop
  no_maximal_time_value : Prop
  no_uncontrolled_higher_derivative : Prop
  no_endpoint_reuse : Prop

end MPrivate.NS.ThirdCoefficient
