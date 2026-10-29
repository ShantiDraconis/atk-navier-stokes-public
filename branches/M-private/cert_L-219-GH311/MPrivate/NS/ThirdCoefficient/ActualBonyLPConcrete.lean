import Mathlib.Basic.Real.Basic
import MPrivate.NS.ThirdCoefficient.ActualBonyDecomposition

namespace MPrivate.NS.ThirdCoefficient.ActualBonyLPConcrete

/-!
Concrete scalar frontier for the low/high Bony route.

Each proposition below isolates one analytic obligation. None is promoted to a
PDE theorem here. The algebra following those obligations is fully proved and
uses no `sorry`, project axiom, endpoint regularity criterion, or circular
`sup Y` / `Z / Y` input.

Important audit convention: the scalar factor used by the closed algebra below
is called `wL`.  This is only the low-vorticity scalar proxy selected for the
candidate route.  If the actual Bony decomposition produces a high-frequency
vorticity factor instead, the actual PDE bridge must not instantiate this proxy
without a separate estimate reducing that factor to the stated `wL` control.
-/

/-- Effective low/high decomposition at the chosen cutoff. The actual
Littlewood--Paley/Bony realization remains an analytic obligation. -/
def BonyEffectiveDecomposition (u uL uH : ℝ) : Prop :=
  u = uL + uH

/-- Scalar product identification representing the chosen Holder cross factor.
Its derivation from the actual PDE blocks remains open.  The name `wL` is kept
consistent with the algebraic theorems below; this definition must not be used
for an actual `wH` block without an additional analytic reduction. -/
def HolderCrossConcrete (uL wL b : ℝ) : Prop :=
  b = uL * wL

/-- High-frequency derivative factor controlled by dissipation. -/
def HighDerivativeFactorSqLeZ (x Z : ℝ) : Prop :=
  x ^ 2 ≤ Z

/-- Low-vorticity squared energy controlled by the total enstrophy variable. -/
def LowVorticityEnergyLeY (wL Y : ℝ) : Prop :=
  wL ^ 2 ≤ Y

/-- Degree-one low-velocity comparison, stated directly in the squared form
needed by the audit-safe algebra below. -/
def VelocityIdentification (uL UL : ℝ) : Prop :=
  uL ^ 2 ≤ UL ^ 2

/-- Minimal sign bookkeeping. This is not a temporal budget and does not
assert T4. -/
def NonCircularitySigns (a3 Y : ℝ) : Prop :=
  0 ≤ a3 ∧ 0 ≤ Y

/-- Audit register for the analytic meaning of the scalar proxies.  These are
obligations only; none is discharged by the scalar algebra in this file. -/
structure ConcreteBonyAnalyticObligations where
  actual_block_inventory_complete : Prop
  chosen_cross_block_identified : Prop
  holder_estimate_for_chosen_block : Prop
  velocity_factor_is_low_frequency : Prop
  vorticity_factor_is_low_energy_controlled : Prop
  high_derivative_factor_is_dissipative : Prop
  projector_L2_bounded : Prop
  derivative_commutes_with_projector : Prop
  shell_sum_or_block_sum_uniform : Prop
  constant_independent_of_target : Prop
  cutoff_from_prior_data_only : Prop
  cutoff_scale_covariant : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_higher_derivative : Prop

/-- Multiplication by the nonnegative velocity square preserves the low-energy
bound. -/
theorem mul_sq_le_mul_sq_of_le {UL wL Y : ℝ}
    (hLow : wL ^ 2 ≤ Y) :
    UL ^ 2 * wL ^ 2 ≤ UL ^ 2 * Y :=
  mul_le_mul_of_nonneg_left hLow (sq_nonneg UL)

/-- Audit-safe cross-product square estimate. -/
theorem uL_wL_sq_le_UL_sq_Y {uL wL UL Y : ℝ}
    (hVel : uL ^ 2 ≤ UL ^ 2)
    (hLow : wL ^ 2 ≤ Y) :
    (uL * wL) ^ 2 ≤ UL ^ 2 * Y := by
  calc
    (uL * wL) ^ 2 = uL ^ 2 * wL ^ 2 := mul_pow uL wL 2
    _ ≤ UL ^ 2 * wL ^ 2 :=
      mul_le_mul_of_nonneg_right hVel (sq_nonneg wL)
    _ ≤ UL ^ 2 * Y :=
      mul_le_mul_of_nonneg_left hLow (sq_nonneg UL)

/-- Once the still-open Bony/Holder factor estimate is supplied, the remaining
transport to the required velocity-square coefficient is purely algebraic. -/
theorem bony_cross_bound {b K uL wL UL Y : ℝ}
    (hBony : b ^ 2 ≤ K ^ 2 * (uL * wL) ^ 2)
    (hCross : (uL * wL) ^ 2 ≤ UL ^ 2 * Y) :
    b ^ 2 ≤ K ^ 2 * UL ^ 2 * Y := by
  calc
    b ^ 2 ≤ K ^ 2 * (uL * wL) ^ 2 := hBony
    _ ≤ K ^ 2 * (UL ^ 2 * Y) :=
      mul_le_mul_of_nonneg_left hCross (sq_nonneg K)
    _ = K ^ 2 * UL ^ 2 * Y := (mul_assoc (K ^ 2) (UL ^ 2) Y).symm

/-- Direct composition of the two closed algebraic steps. The only remaining
analytic input is `hBony`; the velocity and low-energy controls are explicit. -/
theorem bony_cross_bound_from_controls {b K uL wL UL Y : ℝ}
    (hBony : b ^ 2 ≤ K ^ 2 * (uL * wL) ^ 2)
    (hVel : uL ^ 2 ≤ UL ^ 2)
    (hLow : wL ^ 2 ≤ Y) :
    b ^ 2 ≤ K ^ 2 * UL ^ 2 * Y :=
  bony_cross_bound hBony (uL_wL_sq_le_UL_sq_Y hVel hLow)

end MPrivate.NS.ThirdCoefficient.ActualBonyLPConcrete
