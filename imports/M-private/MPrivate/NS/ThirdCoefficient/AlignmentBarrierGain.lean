import Mathlib
import MPrivate.NS.ThirdCoefficient.AlignmentDefectFactorization
import MPrivate.NS.ThirdCoefficient.AlignmentDepletionInequality

namespace MPrivate.NS.ThirdCoefficient

/-!
# AlignmentBarrierGain

A dimensionless defect helps only if it is quantitatively small where the
critical amplitude is large. Merely multiplying a rejected amplitude by a
number in `[0,1]` does not automatically escape the old barrier.
-/

/-- A candidate coefficient reduces to a known amplitude barrier when it
uniformly dominates a fixed positive multiple of that amplitude. This is a
pure comparison predicate; it does not assert that the amplitude itself has a
Navier--Stokes spacetime budget. Positivity excludes the vacuous choice `c = 0`. -/
def ReducesToKnownBarrier (candidate amplitude : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * amplitude t ≤ candidate t

/-- If the alignment defect is bounded below by a positive constant, then the
alignment coefficient still dominates the underlying critical amplitude. -/
theorem positive_defect_preserves_old_barrier
    (A D c : ℝ)
    (hA : 0 ≤ A)
    (hc : 0 < c)
    (hD : c ≤ D) :
    c * A ≤ alignmentCoefficient A D := by
  unfold alignmentCoefficient
  nlinarith

/-- Therefore a uniformly positive defect cannot by itself create an escape
from a rejected amplitude barrier. -/
theorem alignment_reduces_to_amplitude_if_defect_bounded_below
    (A D : ℝ → ℝ)
    (c : ℝ)
    (hc : 0 < c)
    (hA : ∀ t, 0 ≤ A t)
    (hD : ∀ t, c ≤ D t) :
    ReducesToKnownBarrier
      (fun t => alignmentCoefficient (A t) (D t)) A := by
  refine ⟨c, hc, ?_⟩
  intro t
  exact positive_defect_preserves_old_barrier (A t) (D t) c (hA t) hc (hD t)

/-- Genuine pointwise depletion relative to the amplitude requires a defect
strictly below one at the point in question. -/
theorem strict_defect_strictly_reduces_positive_amplitude
    (A D : ℝ)
    (hA : 0 < A)
    (hD0 : 0 ≤ D)
    (hD1 : D < 1) :
    alignmentCoefficient A D < A := by
  unfold alignmentCoefficient
  nlinarith

/-- Endpoint diagnostics: `D=0` kills the factored term, while `D=1` gives no
improvement. The unresolved PDE bridge is to derive useful spacetime control of
`D` from actual Navier--Stokes dynamics. -/
structure AlignmentGainFrontier where
  defect_nonnegative : Prop
  defect_dimensionless : Prop
  signed_factorization : Prop
  defect_strict_gain_on_relevant_set : Prop
  defect_spacetime_budget : Prop
  derived_from_actual_NS : Prop

end MPrivate.NS.ThirdCoefficient
