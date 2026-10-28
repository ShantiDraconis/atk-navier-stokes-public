import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# CrossRemainderScaling

Scaling bookkeeping for the Young remainder in the cross-frequency part.
For the T3 estimate

  Vcross <= eps * Z + C * aCross * Y,

the Young remainder has the same degree as `Vcross` and `Z` (degree 3), while
`Y` has degree 1 and `aCross` must therefore have degree 2.

This file proves only the algebraic homogeneity implications.
-/

/-- Scalar degree-three scaling. -/
def DegreeThree (x xScaled lambda : ℝ) : Prop :=
  xScaled = lambda^3 * x

/-- Scalar degree-one scaling, modeling enstrophy `Y`. -/
def DegreeOne (Y YScaled lambda : ℝ) : Prop :=
  YScaled = lambda * Y

/-- Scalar degree-two scaling, modeling a ThirdCoefficient. -/
def DegreeTwo (a aScaled lambda : ℝ) : Prop :=
  aScaled = lambda^2 * a

/-- A product of a degree-two coefficient and degree-one enstrophy has degree 3. -/
theorem degreeTwo_mul_degreeOne_is_degreeThree
    (a aScaled Y YScaled lambda : ℝ)
    (ha : DegreeTwo a aScaled lambda)
    (hY : DegreeOne Y YScaled lambda) :
    DegreeThree (a * Y) (aScaled * YScaled) lambda := by
  unfold DegreeTwo at ha
  unfold DegreeOne at hY
  unfold DegreeThree
  rw [ha, hY]
  ring

/-- If `b` has degree 3/2, encoded without fractional powers as
`bScaled^2 = lambda^3 * b^2`, then the quadratic Young numerator has degree 3. -/
def CrossFactorSquareScaling
    (b bScaled lambda : ℝ) : Prop :=
  bScaled^2 = lambda^3 * b^2

/-- With scale-invariant positive epsilon, the Young remainder inherits degree 3. -/
theorem young_remainder_degree_three
    (b bScaled eps lambda : ℝ)
    (heps : eps ≠ 0)
    (hb : CrossFactorSquareScaling b bScaled lambda) :
    bScaled^2 / (4 * eps) =
      lambda^3 * (b^2 / (4 * eps)) := by
  unfold CrossFactorSquareScaling at hb
  rw [hb]
  field_simp [heps]

/-- If a Young remainder factors exactly as `C * aCross * Y`, its critical
homogeneity is consistent when `C` is invariant, `aCross` has degree two and
`Y` has degree one. -/
theorem cross_factorization_homogeneity_consistent
    (C a aScaled Y YScaled lambda : ℝ)
    (ha : DegreeTwo a aScaled lambda)
    (hY : DegreeOne Y YScaled lambda) :
    C * aScaled * YScaled = lambda^3 * (C * a * Y) := by
  unfold DegreeTwo at ha
  unfold DegreeOne at hY
  rw [ha, hY]
  ring

end MPrivate.NS.ThirdCoefficient
