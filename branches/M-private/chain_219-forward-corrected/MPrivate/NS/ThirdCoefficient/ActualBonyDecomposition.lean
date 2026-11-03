import Mathlib.Basic.Real.Basic
import MPrivate.NS.ThirdCoefficient.ActualCrossSquareControlFrontier

/--
Analytic frontier for the actual low/high cross interaction.

The fields below are deliberately propositions: this module records exactly which
PDE/LP steps still have to be supplied before the scalar square-control algebra
can be used.  In particular, no Bony identity or Holder/Bernstein estimate is
asserted as a theorem here.
-/
structure ActualBonyDecompositionFrontier where
  bony_identity : Prop
  holder_cross_bound : Prop
  high_derivative_factor_sq_le_Z : Prop
  low_vorticity_energy_le_Y : Prop
  low_velocity_identification : Prop
  target_independent_constant : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_higher_derivative : Prop

/--
Scalar endpoint of the intended Bony route.

`hb` is the still-analytic estimate produced by the actual decomposition and
Holder/Bernstein steps.  Once it is available, the already verified low-energy
and low-velocity identifications imply the required square control.  This
lemma does not prove `hb`.
-/
theorem bony_square_control_algebra
    (b K uLinf omegaL2 UL Y : ℝ)
    (hb : b ^ 2 ≤ K ^ 2 * (uLinf * omegaL2) ^ 2)
    (hU : uLinf = UL)
    (hY : omegaL2 ^ 2 ≤ Y) :
    b ^ 2 ≤ K ^ 2 * (UL ^ 2 * Y) := by
  have hprod : (uLinf * omegaL2) ^ 2 ≤ UL ^ 2 * Y :=
    square_control_algebra uLinf omegaL2 UL Y hU hY
  have hscaled := mul_le_mul_of_nonneg_left hprod (sq_nonneg K)
  exact hb.trans hscaled

/--
The remaining mathematical bridge is explicit: the actual PDE decomposition
must deliver the factor estimate `hb`; this file only transports it to the
square-control form without adding regularity assumptions.
-/
def ActualBonyFactorEstimate
    (b K uLinf omegaL2 : ℝ) : Prop :=
  b ^ 2 ≤ K ^ 2 * (uLinf * omegaL2) ^ 2
