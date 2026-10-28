import Mathlib
import MPrivate.NS.ThirdCoefficient.LowFrequencyAbsorptionAlternative

namespace MPrivate.NS.ThirdCoefficient

/-!
# LowDirectAbsorptionNoGo

A low-frequency Bernstein estimate points in the wrong direction for direct
absorption: it gives an upper bound of the form

  Zlow <= R^2 Ylow,

not a lower bound controlling `Ylow` by `Zlow`. Therefore such an upper bound,
even together with a coefficient-type estimate `Vlow <= R^2 Ylow`, cannot by
itself imply `Vlow <= eps Zlow`.

This is an algebraic insufficiency certificate, not a counterexample to the NSE.
-/

/-- Minimal scalar abstraction of the two low-frequency upper bounds. -/
def LowUpperBounds
    (Vlow Zlow Ylow R : ℝ) : Prop :=
  0 ≤ Zlow ∧
  0 ≤ Ylow ∧
  Zlow ≤ R^2 * Ylow ∧
  Vlow ≤ R^2 * Ylow

/-- Concrete witness: the upper bounds allow positive stretching with zero
`Zlow`, so they cannot force direct absorption. -/
theorem low_upper_bounds_do_not_force_absorption_witness :
    LowUpperBounds 1 0 1 1 ∧
    ¬ LowDirectAbsorption 1 1 0 := by
  constructor
  · unfold LowUpperBounds
    norm_num
  · unfold LowDirectAbsorption
    norm_num

/-- Consequently there is no purely logical implication from `LowUpperBounds`
to unit-coefficient direct absorption for all scalar states. -/
theorem no_universal_low_absorption_from_upper_bounds :
    ¬ (∀ Vlow Zlow Ylow R : ℝ,
        LowUpperBounds Vlow Zlow Ylow R →
        LowDirectAbsorption Vlow 1 Zlow) := by
  intro h
  have hw := h 1 0 1 1 (by
    unfold LowUpperBounds
    norm_num)
  unfold LowDirectAbsorption at hw
  norm_num at hw

/-- To prove low direct absorption one therefore needs extra structure beyond
these upper bounds: sign cancellation, a spectral gap/lower-frequency exclusion,
or another mechanism producing a lower control by dissipation. -/
structure LowAbsorptionExtraStructure where
  signed_cancellation : Prop
  lower_control_by_dissipation : Prop
  spectral_gap_or_equivalent : Prop
  derived_from_actual_NS : Prop

end MPrivate.NS.ThirdCoefficient
