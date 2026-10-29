import Mathlib

/-!
NS-FORCING-001 / quartic Young algebra.

Pure scalar inequality used by the small-data P1 route.
No PDE assumption, no axiom, no sorry.
-/

noncomputable section

namespace NSProducerFirst.P1Concrete

/-- Polynomial Young inequality corresponding to conjugate exponents 4/3 and 4:
    a^3 b <= (3/4) a^4 + (1/4) b^4 for a,b >= 0. -/
theorem quartic_young_three_one
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a^3 * b ≤ (3 / 4 : ℝ) * a^4 + (1 / 4 : ℝ) * b^4 := by
  have hquad : 0 ≤ 3 * a^2 + 2 * a * b + b^2 := by
    nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg ha hb]
  have hfac :
      0 ≤ (a - b)^2 * (3 * a^2 + 2 * a * b + b^2) :=
    mul_nonneg (sq_nonneg (a - b)) hquad
  have hid :
      (a - b)^2 * (3 * a^2 + 2 * a * b + b^2) =
        3 * a^4 - 4 * a^3 * b + b^4 := by
    ring
  rw [hid] at hfac
  nlinarith

/-- Equivalent denominator-free form, convenient for later scaled substitutions. -/
theorem quartic_young_three_one_four_mul
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * (a^3 * b) ≤ 3 * a^4 + b^4 := by
  nlinarith [quartic_young_three_one a b ha hb]

#print axioms NSProducerFirst.P1Concrete.quartic_young_three_one
#print axioms NSProducerFirst.P1Concrete.quartic_young_three_one_four_mul

end NSProducerFirst.P1Concrete
