import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# LowFrequencyAbsorptionAlternative

If the low-frequency contribution can be absorbed into dissipation, it should
not be encoded as a positive time-constant coefficient.  Taking `aLow = 0`
then avoids the linear-in-time T4 obstruction.
-/

/-- Direct low-frequency absorption target. -/
def LowDirectAbsorption
    (Vlow epsLow Z : ℝ) : Prop :=
  Vlow ≤ epsLow * Z

/-- Zero is nonnegative and is the ideal low coefficient if direct absorption
is available. -/
theorem zero_low_coefficient_nonnegative :
    0 ≤ (0 : ℝ) := by norm_num

/-- Zero has degree two under every scaling law, trivially. -/
theorem zero_low_coefficient_critical
    (lambda : ℝ) :
    (0 : ℝ) = lambda^2 * 0 := by ring

/-- Direct absorption turns the low block into a pure dissipative contribution,
so no `aLow * Y` term is needed. -/
theorem low_direct_absorption_zero_coefficient
    (Vlow epsLow Z C Y : ℝ)
    (h : LowDirectAbsorption Vlow epsLow Z) :
    Vlow ≤ epsLow * Z + C * 0 * Y := by
  unfold LowDirectAbsorption at h
  simpa using h

/-- Two separately absorbed signed blocks combine by adding their epsilon
budgets. -/
theorem combine_two_absorbed_blocks
    (V1 V2 eps1 eps2 Z : ℝ)
    (h1 : V1 ≤ eps1 * Z)
    (h2 : V2 ≤ eps2 * Z) :
    V1 + V2 ≤ (eps1 + eps2) * Z := by
  linarith

/-- To preserve a strict G1-flex margin, the total absorbed fraction must stay
strictly below viscosity. -/
def AbsorptionBudgetAdmissible
    (epsTotal nu : ℝ) : Prop :=
  0 ≤ epsTotal ∧ epsTotal < nu

end MPrivate.NS.ThirdCoefficient
