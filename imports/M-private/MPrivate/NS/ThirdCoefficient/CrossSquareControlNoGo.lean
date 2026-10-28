import Mathlib
import MPrivate.NS.ThirdCoefficient.CrossVelocityFactorization

namespace MPrivate.NS.ThirdCoefficient

/-!
# CrossSquareControlNoGo

Necessary algebraic conditions for the velocity-square cross candidate.

These results do not assert the actual Navier--Stokes cross estimate. They show
that any proof of

  b^2 ≤ K^2 * U^2 * Y

must force the Young factor `b` to vanish whenever either `Y` or the chosen
velocity amplitude `U` vanishes. Hence a concrete cross representation with
nonzero `b` in either regime refutes this entire square-control ansatz.
-/

/-- If enstrophy `Y` vanishes, square control forces the Young factor to vanish. -/
theorem crossSquareControl_zero_Y_forces_b_zero
    (b K U : ℝ)
    (h : CrossSquareControl b K U 0) :
    b = 0 := by
  unfold CrossSquareControl at h
  have hb2 : b^2 ≤ 0 := by simpa using h
  nlinarith [sq_nonneg b]

/-- If the low-velocity amplitude vanishes, square control forces the Young
factor to vanish, independently of `Y`. -/
theorem crossSquareControl_zero_U_forces_b_zero
    (b K Y : ℝ)
    (h : CrossSquareControl b K 0 Y) :
    b = 0 := by
  unfold CrossSquareControl at h
  have hb2 : b^2 ≤ 0 := by simpa using h
  nlinarith [sq_nonneg b]

/-- Nonzero `b` at zero enstrophy is a direct obstruction to this cross
square-control class. -/
theorem no_crossSquareControl_if_zero_Y_and_b_nonzero
    (b K U : ℝ)
    (hb : b ≠ 0) :
    ¬ CrossSquareControl b K U 0 := by
  intro h
  exact hb (crossSquareControl_zero_Y_forces_b_zero b K U h)

/-- Nonzero `b` at zero low-velocity amplitude is a direct obstruction to this
cross square-control class. -/
theorem no_crossSquareControl_if_zero_U_and_b_nonzero
    (b K Y : ℝ)
    (hb : b ≠ 0) :
    ¬ CrossSquareControl b K 0 Y := by
  intro h
  exact hb (crossSquareControl_zero_U_forces_b_zero b K Y h)

/-- Exact unresolved PDE question after the algebraic NoGo certificates above. -/
structure CrossSquareControlPDEFrontier where
  actual_cross_representation : Prop
  actual_b_definition : Prop
  actual_low_velocity_amplitude : Prop
  actual_enstrophy_identification : Prop
  square_control_from_NSE : Prop
  zero_Y_compatibility : Prop
  zero_U_compatibility : Prop
  K_uniform_and_target_independent : Prop

end MPrivate.NS.ThirdCoefficient
