import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# CrossTermYoungAbsorption

Pure algebraic certificates for the cross-frequency part of T3.
The analytic PDE work is reduced to identifying quantities `x` and `b` such
that the cross interaction is bounded by `x*b`, with `x^2` controlled by `Z`.
-/

/-- Elementary Young inequality in the form needed for T3. -/
theorem young_product_absorption
    (x b eps : ℝ)
    (heps : 0 < eps) :
    x * b ≤ eps * x^2 + b^2 / (4 * eps) := by
  have hsquare : 0 ≤ (2 * eps * x - b)^2 := sq_nonneg (2 * eps * x - b)
  have heps0 : eps ≠ 0 := ne_of_gt heps
  field_simp [heps0]
  nlinarith

/-- If the dissipative factor `x^2` is bounded by `Z`, Young absorbs the cross
interaction into `eps Z` plus a coefficient term. -/
theorem cross_absorbed_if_square_le_Z
    (Vcross x b Z eps : ℝ)
    (heps : 0 < eps)
    (hV : Vcross ≤ x * b)
    (hx : x^2 ≤ Z) :
    Vcross ≤ eps * Z + b^2 / (4 * eps) := by
  have hy := young_product_absorption x b eps heps
  have hepsnonneg : 0 ≤ eps := le_of_lt heps
  nlinarith

/-- T3 needs the Young remainder to factor through `Y`.  This predicate is kept
explicit because proving it for the actual spectral cross term is analytic,
not algebraic. -/
def CrossRemainderFactorsThroughY
    (b eps C aCross Y : ℝ) : Prop :=
  b^2 / (4 * eps) ≤ C * aCross * Y

/-- Assembly of cross absorption with the required factorization. -/
theorem cross_T3_from_young_and_factorization
    (Vcross x b Z eps C aCross Y : ℝ)
    (heps : 0 < eps)
    (hV : Vcross ≤ x * b)
    (hx : x^2 ≤ Z)
    (hfactor : CrossRemainderFactorsThroughY b eps C aCross Y) :
    Vcross ≤ eps * Z + C * aCross * Y := by
  have hcross := cross_absorbed_if_square_le_Z Vcross x b Z eps heps hV hx
  unfold CrossRemainderFactorsThroughY at hfactor
  linarith

end MPrivate.NS.ThirdCoefficient
