import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-- Critical time exponent associated with a spatial `L^p` norm of strain or vorticity. -/
noncomputable def criticalQ (p : ℝ) : ℝ := 2 * p / (2 * p - 3)

/-- Algebraic identity behind the critical scaling condition
    `q * (2 - 3/p) = 2`. -/
theorem criticalQ_identity {p : ℝ} (hp : p ≠ 0) (hden : 2 * p - 3 ≠ 0) :
    criticalQ p * (2 - 3 / p) = 2 := by
  unfold criticalQ
  field_simp [hp, hden]

/-- For `p > 3/2`, the critical time exponent is positive. -/
theorem criticalQ_pos {p : ℝ} (hp : (3 : ℝ) / 2 < p) : 0 < criticalQ p := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < 2 * p - 3 := by linarith
  exact div_pos (mul_pos (by norm_num) hp0) hden

/-- At `p = 3`, the critical exponent is exactly `q = 2`. -/
theorem criticalQ_three : criticalQ 3 = 2 := by
  norm_num [criticalQ]

end MPrivate.NS.ThirdCoefficient
