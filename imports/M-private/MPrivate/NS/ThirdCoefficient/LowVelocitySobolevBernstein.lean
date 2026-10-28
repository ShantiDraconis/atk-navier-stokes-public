import Mathlib
import MPrivate.NS.ThirdCoefficient.ActualBonyDecomposition
import MPrivate.NS.ThirdCoefficient.ActualCrossBudget

namespace MPrivate.NS.ThirdCoefficient

/-!
# LowVelocitySobolevBernstein

Audit-safe reduction for the *same* `UL` appearing in the certified Bony/T3
route.  `ActualBonyDecomposition` explicitly identifies that scalar with the
low-frequency L-infinity velocity factor (`uLinf = UL`).

The admissible analytic route is

  ||P_{<=M} u||_infinity <= C_B M^(1/2) ||P_{<=M} u||_6
                         <= C_B M^(1/2) ||u||_6
                         <= C_B C_S M^(1/2) ||grad u||_2.

After squaring,

  UL^2 <= (C_B C_S)^2 M ||grad u||_2^2.

This is not a reverse Poincare estimate.  It uses low-frequency Bernstein from
L6 to L-infinity plus the energy-level Sobolev embedding H1 -> L6.
The file below closes only the scalar composition.  The concrete LP/Sobolev
realization on the actual Navier--Stokes solution remains an analytic bridge.
-/

/-- Squared low-pass Bernstein input corresponding to
`||P_{<=M}u||_infinity <= C_B M^(1/2) ||u||_6`. -/
def LowPassBernsteinL6ToLinfSq
    (UL u6 M CB : ℝ) : Prop :=
  0 ≤ M ∧ 0 ≤ CB ∧ UL ^ 2 ≤ CB ^ 2 * M * u6 ^ 2

/-- Squared Sobolev input corresponding to
`||u||_6 <= C_S ||grad u||_2`, with `g = ||grad u||_2^2`. -/
def SobolevL6FromGradientSq
    (u6 g CS : ℝ) : Prop :=
  0 ≤ g ∧ 0 ≤ CS ∧ u6 ^ 2 ≤ CS ^ 2 * g

/-- Bernstein L6->Linf followed by Sobolev H1->L6 gives the correct critical
pointwise multiplier for the exact low-velocity square used by T3. -/
theorem low_velocity_square_le_cutoff_times_gradient
    (UL u6 g M CB CS : ℝ)
    (hB : LowPassBernsteinL6ToLinfSq UL u6 M CB)
    (hS : SobolevL6FromGradientSq u6 g CS) :
    UL ^ 2 ≤ (CB * CS) ^ 2 * M * g := by
  rcases hB with ⟨hM, hCB, hUL⟩
  rcases hS with ⟨hg, hCS, hu6⟩
  have hfactor : 0 ≤ CB ^ 2 * M := mul_nonneg (sq_nonneg CB) hM
  have hstep :
      CB ^ 2 * M * u6 ^ 2 ≤ CB ^ 2 * M * (CS ^ 2 * g) :=
    mul_le_mul_of_nonneg_left hu6 hfactor
  calc
    UL ^ 2 ≤ CB ^ 2 * M * u6 ^ 2 := hUL
    _ ≤ CB ^ 2 * M * (CS ^ 2 * g) := hstep
    _ = (CB * CS) ^ 2 * M * g := by ring

/-- Pointwise-in-time version, ready to instantiate with the actual low-pass
velocity, L6 norm, and gradient-energy density. -/
theorem low_velocity_square_energy_gain_from_bernstein_sobolev
    (UL u6 g : ℝ → ℝ)
    (M CB CS : ℝ)
    (hB : ∀ t, LowPassBernsteinL6ToLinfSq (UL t) (u6 t) M CB)
    (hS : ∀ t, SobolevL6FromGradientSq (u6 t) (g t) CS) :
    LowVelocitySquareEnergyGain UL g ((CB * CS) ^ 2 * M) := by
  have hM : 0 ≤ M := (hB 0).1
  refine ⟨mul_nonneg (sq_nonneg (CB * CS)) hM, ?_⟩
  intro t
  exact low_velocity_square_le_cutoff_times_gradient
    (UL t) (u6 t) (g t) M CB CS (hB t) (hS t)

/-- Full scalar bookkeeping from the Bernstein--Sobolev bridge to the uniform
cross budget.  The cross coefficient is not changed: it remains
`aCross(t) = A * UL(t)^2`, exactly the form produced by the T3 algebra. -/
theorem uniform_cross_budget_from_bernstein_sobolev
    (I : (ℝ → ℝ) → ℝ → ℝ)
    (hmono : IntegralMonotone I)
    (hmul : IntegralConstMul I)
    (aCross UL u6 g : ℝ → ℝ)
    (A M CB CS Tstar E0 nu : ℝ)
    (hA : 0 ≤ A)
    (hcoef : ∀ t, aCross t = A * UL t ^ 2)
    (hB : ∀ t, LowPassBernsteinL6ToLinfSq (UL t) (u6 t) M CB)
    (hS : ∀ t, SobolevL6FromGradientSq (u6 t) (g t) CS)
    (henergy : UniformEnergyBudgetBelow I g Tstar E0 nu) :
    UniformCrossBudgetBelow I aCross Tstar
      ((A * ((CB * CS) ^ 2 * M)) * (E0 / (2 * nu))) := by
  exact uniform_cross_budget_from_low_velocity_square_gain
    I hmono hmul aCross UL g A ((CB * CS) ^ 2 * M) Tstar E0 nu
    hA hcoef
    (low_velocity_square_energy_gain_from_bernstein_sobolev UL u6 g M CB CS hB hS)
    henergy

/-- Exact analytic obligations that remain before this standard harmonic-
analysis route can be instantiated on the actual NSE solution. -/
structure LowVelocitySobolevBernsteinFrontier where
  same_UL_as_ActualBonyToCrossT3 : Prop
  UL_is_actual_lowpass_Linfinity_velocity_norm : Prop
  same_cutoff_as_T3 : Prop
  cutoff_positive : Prop
  cutoff_initial_data_only : Prop
  cutoff_scale_covariant : Prop
  lowpass_projector_L6_bounded : Prop
  bernstein_L6_to_Linfinity_for_actual_projector : Prop
  homogeneous_sobolev_H1_to_L6_on_R3 : Prop
  gradient_density_is_actual_grad_u_L2_sq : Prop
  same_solution_and_interval : Prop
  same_viscosity_as_energy_balance : Prop
  estimates_hold_for_every_t_below_Tstar : Prop
  constants_independent_of_t_and_Tstar : Prop
  constants_independent_of_future_solution : Prop
  no_reverse_lowpass_poincare : Prop
  no_energy_for_enstrophy_substitution : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_future_critical_norm : Prop
  no_endpoint_reuse : Prop
  no_uncontrolled_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient
