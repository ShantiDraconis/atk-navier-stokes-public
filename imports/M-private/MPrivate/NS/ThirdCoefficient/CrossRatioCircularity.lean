import Mathlib
import MPrivate.NS.ThirdCoefficient.CrossTermYoungAbsorption

namespace MPrivate.NS.ThirdCoefficient

/-!
# CrossRatioCircularity

The exact algebraic way to force the Young remainder

  b^2/(4 eps)

to equal `C * aCross * Y` is to divide by `Y`.  That construction is precisely
the type of target-dependent ratio excluded by T6.  This file records the
identity and the singularity explicitly so it cannot be smuggled into a
candidate under a different name.
-/

/-- Exact ratio coefficient associated with the Young remainder. -/
noncomputable def exactCrossRatioCoefficient
    (b eps C Y : ℝ) : ℝ :=
  b^2 / (4 * eps * C * Y)

/-- Away from zero denominators the ratio coefficient reproduces the Young
remainder exactly. -/
theorem exact_cross_ratio_factorization
    (b eps C Y : ℝ)
    (heps : eps ≠ 0)
    (hC : C ≠ 0)
    (hY : Y ≠ 0) :
    C * exactCrossRatioCoefficient b eps C Y * Y =
      b^2 / (4 * eps) := by
  unfold exactCrossRatioCoefficient
  field_simp [heps, hC, hY]

/-- The construction depends explicitly on division by the target enstrophy. -/
def UsesYDenominator (uses : Prop) : Prop := uses

/-- Audit marker: the exact ratio construction is a Y-denominator construction. -/
theorem exact_cross_ratio_uses_Y_denominator :
    UsesYDenominator True := by
  trivial

/-- At `Y = 0`, the literal ratio formula collapses to division by zero in the
field convention and cannot represent a generally positive Young remainder. -/
theorem zero_Y_ratio_cannot_match_positive_remainder
    (b eps C : ℝ)
    (hb : b ≠ 0)
    (heps : 0 < eps) :
    C * exactCrossRatioCoefficient b eps C 0 * 0 = 0 ∧
    0 < b^2 / (4 * eps) := by
  constructor
  · simp [exactCrossRatioCoefficient]
  · have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
    positivity

/-- A valid `aCross` must therefore be obtained by an independent factorization
or estimate, not by defining it as the remainder divided by `Y`. -/
structure CrossNonCircularFrontier where
  young_remainder_bound : Prop
  independent_aCross_definition : Prop
  remainder_factors_through_Y : Prop
  no_Y_denominator : Prop
  no_Z_div_Y : Prop
  L1_budget_independent_of_target : Prop

end MPrivate.NS.ThirdCoefficient
