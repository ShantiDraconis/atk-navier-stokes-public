import Mathlib
import G1_KAdmissible_to_SignedDepletion

namespace MillenniumAudit.G1PrimitiveLaws

/--
Raw bulk-tail-remainder inequality with no certificate or OpenMath argument.

Inputs are only scalar identities/inequalities at one time t.
-/
theorem raw_bulk_tail_remainder_bound
    (stretch bulk tail remainder ν z y a cBulk cTail : ℝ)
    (hsplit : stretch = bulk + tail + remainder)
    (hbulk : bulk ≤ cBulk * ν * z)
    (htail : tail ≤ cTail * ν * z)
    (hrem : remainder ≤ a * y) :
    stretch ≤ (cBulk + cTail) * ν * z + a * y := by
  rw [hsplit]
  nlinarith

/--
Raw enstrophy differential law.

From y'/2 + ν z = stretch and the raw geometric bound, derive the exact
differential inequality without passing a SignedDepletion/OpenMath object.
-/
theorem raw_enstrophy_differential
    (yPrime stretch ν z y a cBulk cTail : ℝ)
    (hbalance : yPrime / 2 + ν * z = stretch)
    (hstretch :
      stretch ≤ (cBulk + cTail) * ν * z + a * y) :
    yPrime + 2 * (1 - (cBulk + cTail)) * ν * z ≤
      2 * a * y := by
  linarith

/-- Strict positive dissipation margin is exactly the scalar budget law. -/
theorem raw_budget_gives_positive_margin
    (cBulk cTail : ℝ)
    (hbudget : cBulk + cTail < 1) :
    0 < 1 - (cBulk + cTail) := by
  linarith

/--
Raw time-budget composition.

If the coefficient integral is bounded by K times the total gradient energy,
and Leray energy bounds that total gradient energy by E/(2ν), then the
coefficient integral has the explicit composed bound K*E/(2ν).

No GronwallCertificate or endpoint proposition is an input.
-/
theorem raw_time_coefficient_budget
    (totalA totalGradU2 K E ν : ℝ)
    (hK : 0 ≤ K)
    (hA : totalA ≤ K * totalGradU2)
    (hEnergy : totalGradU2 ≤ E / (2 * ν)) :
    totalA ≤ K * (E / (2 * ν)) := by
  exact hA.trans (mul_le_mul_of_nonneg_left hEnergy hK)

/--
Zero remainder is the strict special case.
-/
theorem raw_zero_remainder_differential
    (yPrime stretch ν z cBulk cTail : ℝ)
    (hbalance : yPrime / 2 + ν * z = stretch)
    (hstretch : stretch ≤ (cBulk + cTail) * ν * z) :
    yPrime + 2 * (1 - (cBulk + cTail)) * ν * z ≤ 0 := by
  linarith

#print axioms MillenniumAudit.G1PrimitiveLaws.raw_bulk_tail_remainder_bound
#print axioms MillenniumAudit.G1PrimitiveLaws.raw_enstrophy_differential
#print axioms MillenniumAudit.G1PrimitiveLaws.raw_budget_gives_positive_margin
#print axioms MillenniumAudit.G1PrimitiveLaws.raw_time_coefficient_budget
#print axioms MillenniumAudit.G1PrimitiveLaws.raw_zero_remainder_differential

end MillenniumAudit.G1PrimitiveLaws
