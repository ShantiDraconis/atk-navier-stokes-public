import Mathlib
import MPrivate.NS.ThirdCoefficient.AlignmentDepletionInequality

namespace MPrivate.NS.ThirdCoefficient

/-!
Regression certificates for the first failing point in the signed route.
They ensure that T2 is a genuine NSE covariance requirement and that T3 cannot
collapse to the unintended `V ≤ 0` statement by universally quantifying over
zero constants.
-/

/-- A constant coefficient cannot satisfy degree-two critical scaling under an
identity state scaling. This would have passed the previous tautological T2. -/
theorem constant_one_not_scaleCritical :
    ¬ ScaleCritical (fun (_lambda : ℝ) (u : Unit) => u)
        (fun (_u : Unit) (_t : Time) => (1 : ℝ)) := by
  intro h
  have h2 := h () 2 0 (by norm_num)
  norm_num at h2

/-- T3 requires a strictly positive dissipative coefficient `ε`; therefore
`ε = 0` is rejected at the specification layer. -/
theorem zero_epsilon_not_signedDominates
    {State : Type*}
    (V Z Y a3 : State → Time → ℝ)
    (C : ℝ) :
    ¬ SignedDominatesStretching V Z Y a3 0 C := by
  intro h
  exact (lt_irrefl 0) h.1

/-- T3 does not require absolute-value control of the signed producer. -/
theorem signed_target_is_one_sided
    {State : Type*}
    (V Z Y a3 : State → Time → ℝ)
    (ε C : ℝ)
    (h : SignedDominatesStretching V Z Y a3 ε C) :
    ∀ u t, V u t ≤ ε * Z u t + C * a3 u t * Y u t := by
  exact h.2.2

end MPrivate.NS.ThirdCoefficient
