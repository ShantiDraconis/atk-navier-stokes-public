import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# EnergyMultiplierScaling

For positive Navier--Stokes scaling in 3D:

* a ThirdCoefficient has degree +2;
* the instantaneous kinetic-energy dissipation density `||grad u||_2^2`
  has degree +1;
* the time-integrated energy budget / initial L2 energy has degree -1.

Therefore a pointwise estimate

  a <= Cstar * ||grad u||_2^2

is scaling-compatible only when `Cstar` has degree +1.  Then the integrated
budget `Cstar * E0` is scale invariant.
-/

/-- Degree-one multiplier. -/
def DegreeOneMultiplier (C Cscaled lambda : ℝ) : Prop :=
  Cscaled = lambda * C

/-- Degree-one gradient-energy density. -/
def DegreeOneEnergyDensity (g gScaled lambda : ℝ) : Prop :=
  gScaled = lambda * g

/-- Degree-minus-one initial kinetic energy. -/
def DegreeMinusOneEnergy (E Escaled lambda : ℝ) : Prop :=
  lambda * Escaled = E

/-- Degree-one multiplier times degree-one dissipation density has degree two. -/
theorem multiplier_times_energy_density_degree_two
    (C Cscaled g gScaled lambda : ℝ)
    (hC : DegreeOneMultiplier C Cscaled lambda)
    (hg : DegreeOneEnergyDensity g gScaled lambda) :
    Cscaled * gScaled = lambda^2 * (C * g) := by
  unfold DegreeOneMultiplier at hC
  unfold DegreeOneEnergyDensity at hg
  rw [hC, hg]
  ring

/-- Degree-one multiplier times degree-minus-one initial energy is invariant
under positive NS scaling. -/
theorem multiplier_times_initial_energy_invariant
    (C Cscaled E Escaled lambda : ℝ)
    (hlambda : 0 < lambda)
    (hC : DegreeOneMultiplier C Cscaled lambda)
    (hE : DegreeMinusOneEnergy E Escaled lambda) :
    Cscaled * Escaled = C * E := by
  have hlambda0 : lambda ≠ 0 := ne_of_gt hlambda
  unfold DegreeOneMultiplier at hC
  unfold DegreeMinusOneEnergy at hE
  rw [hC]
  have hEscaled : Escaled = E / lambda := by
    apply (eq_div_iff hlambda0).2
    simpa [mul_comm] using hE
  rw [hEscaled]
  field_simp [hlambda0]

/-- A scale-invariant multiplier cannot generically repair the missing degree in
`a <= Cstar * g` when `g` has only degree +1. -/
theorem invariant_multiplier_wrong_degree_witness :
    let C : ℝ := 1
    let g : ℝ := 1
    let lambda : ℝ := 2
    (C * (lambda * g) : ℝ) ≠ lambda^2 * (C * g) := by
  norm_num

/-- Analytic frontier for the energy-budget strategy. -/
structure DegreeOneMultiplierFrontier where
  multiplier_constructed_from_initial_data : Prop
  multiplier_degree_one_for_all_positive_scales : Prop
  multiplier_finite : Prop
  multiplier_nonnegative_when_used_monotonically : Prop
  pointwise_third_coefficient_bound : Prop
  viscosity_convention_compatible : Prop
  multiplier_uniform_below_Tstar : Prop
  multiplier_independent_of_Tstar : Prop
  multiplier_independent_of_future_target : Prop
  no_critical_endpoint_reuse : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_hidden_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient
