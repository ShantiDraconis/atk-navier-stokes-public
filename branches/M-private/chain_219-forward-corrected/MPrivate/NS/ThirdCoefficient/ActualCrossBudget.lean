import Mathlib
import MPrivate.NS.ThirdCoefficient.EnergyBudgetMultiplier
import MPrivate.NS.ThirdCoefficient.ScaleInvariantBudget
import MPrivate.NS.ThirdCoefficient.CrossLowVelocityTimeBudgetNoGo

namespace MPrivate.NS.ThirdCoefficient

/-!
# ActualCrossBudget

Audit-safe closure of the *bookkeeping* part of the cross T4 budget.

Two sufficient routes are recorded here:

1. a pointwise multiplier estimate, as in `EnergyBudgetMultiplier`;
2. a strictly weaker integrated gain

   `I aCross T <= Cstar * I g T`

   on every finite `T < Tstar`.

The second route is important because it does **not** require a pointwise
low-frequency inequality such as `UL^2 <= B * g`.  Neither route is counted as
an ActualNS theorem until its gain hypothesis is derived from the actual PDE
with the provenance and non-circularity gates stated below.
-/

variable (I : (ℝ → ℝ) → ℝ → ℝ)

/-- Uniform cross budget on every finite interval below a candidate maximal
lifetime.  The budget value is independent of `T`. -/
def UniformCrossBudgetBelow
    (aCross : ℝ → ℝ) (Tstar BC : ℝ) : Prop :=
  ∀ T, 0 ≤ T → T < Tstar → I aCross T ≤ BC

/-- Uniform kinetic-energy budget on every finite interval below `Tstar`. -/
def UniformEnergyBudgetBelow
    (g : ℝ → ℝ) (Tstar E0 nu : ℝ) : Prop :=
  ∀ T, 0 ≤ T → T < Tstar → EnergyIntegralBudget I g T E0 nu

/-- Pointwise spacetime gain for the cross coefficient. -/
def CrossSpacetimeEnergyGain
    (aCross g : ℝ → ℝ) (Cstar : ℝ) : Prop :=
  EnergyMultiplierPointwise aCross g Cstar

/-- Integrated spacetime gain.  This is weaker than a pointwise multiplier
bound and is sufficient for T4 once the ordinary energy integral budget is
available. -/
def CrossIntegratedEnergyGain
    (aCross g : ℝ → ℝ) (Cstar Tstar : ℝ) : Prop :=
  0 ≤ Cstar ∧
  ∀ T, 0 ≤ T → T < Tstar → I aCross T ≤ Cstar * I g T

/-- Pointwise route: once the cross coefficient has a genuine pointwise
reduction to the energy dissipation density, the T4 cross budget is uniform for
every `T < Tstar`. -/
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

/-- Integrated route: no pointwise estimate is needed.  A uniform integrated
comparison of the actual cross coefficient with the actual energy dissipation
integral is already enough to close the cross T4 budget. -/
theorem uniform_cross_budget_from_integrated_gain
    (aCross g : ℝ → ℝ)
    (Cstar Tstar E0 nu : ℝ)
    (hgain : CrossIntegratedEnergyGain I aCross g Cstar Tstar)
    (henergy : UniformEnergyBudgetBelow I g Tstar E0 nu) :
    UniformCrossBudgetBelow I aCross Tstar
      (Cstar * (E0 / (2 * nu))) := by
  rcases hgain with ⟨hC, hgain⟩
  intro T hT hTstar
  have hcross : I aCross T ≤ Cstar * I g T := hgain T hT hTstar
  rcases henergy T hT hTstar with ⟨hnu, hE0, henergyT⟩
  exact hcross.trans (mul_le_mul_of_nonneg_left henergyT hC)

/-- Squared low-velocity amplitudes are pointwise nonnegative. -/
theorem low_velocity_square_nonnegative
    (UL : ℝ → ℝ) :
    ∀ t, 0 ≤ UL t ^ 2 := by
  intro t
  exact sq_nonneg (UL t)

/-- The genuinely unresolved analytic content needed to upgrade this file from
conditional bookkeeping to an ActualNS cross-budget certificate.  The audit
accepts either a valid pointwise gain or a valid integrated gain; the latter is
specifically designed to avoid an unjustified reverse low-pass Poincare step. -/
structure ActualCrossBudgetFrontier where
  actual_solution_class_identified : Prop
  maximal_lifetime_is_actual_solution_lifetime : Prop
  maximal_lifetime_positive : Prop
  actual_cross_coefficient_identified : Prop
  coefficient_measurable : Prop
  coefficient_nonnegative : Prop
  kinetic_energy_density_identified : Prop
  kinetic_energy_density_measurable : Prop
  kinetic_energy_density_nonnegative : Prop
  integrated_spacetime_gain_from_actual_NS : Prop
  integrated_gain_uniform_for_every_T_below_Tstar : Prop
  integrated_gain_uses_same_solution_and_interval : Prop
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
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_future_critical_norm : Prop
  no_maximal_time_value : Prop
  no_endpoint_reuse : Prop
  no_uncontrolled_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient
