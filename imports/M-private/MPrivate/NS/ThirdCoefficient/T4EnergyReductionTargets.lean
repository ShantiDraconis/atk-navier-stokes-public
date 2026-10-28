import Mathlib
import MPrivate.NS.ThirdCoefficient.EnergyBudgetMultiplier
import MPrivate.NS.ThirdCoefficient.EnergyMultiplierScaling

namespace MPrivate.NS.ThirdCoefficient

/-!
# T4EnergyReductionTargets

Preferred non-circular T4 reduction.

The combined critical coefficient has degree +2. The basic kinetic-energy
dissipation density `g(t)=||grad u(t)||_2^2` has degree +1. Therefore a
scale-compatible energy reduction must have the form

  aCross(t) + aAlign(t) <= Cstar(u0) * g(t),

where `Cstar` has degree +1. If `Cstar` is determined from initial data and the
energy inequality controls the time integral of `g`, T4 closes algebraically.
-/

/-- Pointwise combined energy-reduction target. -/
def CrossAlignEnergyReduction
    (aCross aAlign g : ℝ → ℝ) (Cstar : ℝ) : Prop :=
  0 ≤ Cstar ∧ ∀ t, aCross t + aAlign t ≤ Cstar * g t

/-- The target directly matches the generic energy-multiplier theorem. -/
theorem cross_align_energy_reduction_gives_T4
    (I : (ℝ → ℝ) → ℝ → ℝ)
    (hmono : IntegralMonotone I)
    (hmul : IntegralConstMul I)
    (aCross aAlign g : ℝ → ℝ)
    (Cstar T E0 nu : ℝ)
    (hred : CrossAlignEnergyReduction aCross aAlign g Cstar)
    (henergy : EnergyIntegralBudget I g T E0 nu) :
    I (fun t => aCross t + aAlign t) T ≤
      Cstar * (E0 / (2 * nu)) := by
  rcases hred with ⟨hC, hpoint⟩
  exact energy_multiplier_closes_cross_align_sum
    I hmono hmul aCross aAlign g Cstar T E0 nu hC hpoint henergy

/-- Scaling consistency of the pointwise right-hand side. -/
theorem energy_reduction_rhs_has_degree_two
    (C CScaled g gScaled lambda : ℝ)
    (hC : DegreeOneMultiplier C CScaled lambda)
    (hg : DegreeOneEnergyDensity g gScaled lambda) :
    CScaled * gScaled = lambda^2 * (C * g) :=
  multiplier_times_energy_density_degree_two C CScaled g gScaled lambda hC hg

/-- Concrete analytic obligations for the combined reduction. -/
structure CombinedEnergyReductionFrontier where
  cross_coefficient_constructed : Prop
  alignment_coefficient_constructed : Prop
  coefficients_nonnegative : Prop
  coefficients_measurable : Prop
  gradient_energy_density_identified : Prop
  gradient_energy_density_nonnegative : Prop
  degree_one_initial_multiplier_constructed : Prop
  multiplier_scale_covariant : Prop
  pointwise_combined_reduction : Prop
  multiplier_finite_for_admissible_data : Prop
  multiplier_initial_data_only : Prop
  energy_budget_on_every_finite_subinterval : Prop
  finite_time_bound_uniform_below_Tstar : Prop
  passage_to_maximal_interval_justified : Prop
  viscosity_positive : Prop
  no_hidden_time_length_factor : Prop
  no_L3_endpoint : Prop
  no_future_critical_norm : Prop
  no_maximal_time_value : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_higher_derivative : Prop
  no_global_conclusion_reuse : Prop
  actualNS_derivation : Prop

/-- If this frontier is closed, the time-integrability part of T4 follows from
the basic energy budget; it does not by itself prove T3. -/
inductive T4EnergyRouteStatus where
  | algebraicImplicationProved
  | analyticPointwiseReductionOpen
  | refuted
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
