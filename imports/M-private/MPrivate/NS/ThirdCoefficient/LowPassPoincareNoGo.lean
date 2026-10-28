import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# LowPassPoincareNoGo

For a low-pass component one has the Bernstein-type direction

  ||grad f_L|| <= R ||f_L||,

not the reverse estimate

  ||f_L|| <= R^{-1} ||grad f_L||.

A reverse inequality needs additional information such as removal of the zero
mode, annular spectral support, a mean-zero condition on a bounded domain, or a
genuine spectral gap.  This file records the scalar logical obstruction so the
reverse inequality cannot be imported from a low-pass label alone.
-/

/-- Scalar abstraction of low-pass Bernstein information. -/
def LowPassBernstein (f grad R : ℝ) : Prop :=
  0 ≤ f ∧ 0 ≤ grad ∧ 0 < R ∧ grad ≤ R * f

/-- Reverse Poincare target sometimes (incorrectly) inferred from low-pass support. -/
def ReverseLowPassPoincare (f grad R : ℝ) : Prop :=
  f ≤ grad / R

/-- Low-pass Bernstein alone does not force the reverse inequality. -/
theorem lowpass_bernstein_does_not_imply_reverse_witness :
    LowPassBernstein 1 0 1 ∧
    ¬ ReverseLowPassPoincare 1 0 1 := by
  constructor
  · unfold LowPassBernstein
    norm_num
  · unfold ReverseLowPassPoincare
    norm_num

/-- Hence there is no universal implication from the low-pass Bernstein upper
bound to the reverse Poincare estimate. -/
theorem no_reverse_poincare_from_lowpass_bernstein :
    ¬ (∀ f grad R : ℝ,
        LowPassBernstein f grad R →
        ReverseLowPassPoincare f grad R) := by
  intro h
  have hw := h 1 0 1 (by
    unfold LowPassBernstein
    norm_num)
  unfold ReverseLowPassPoincare at hw
  norm_num at hw

/-- Extra structure that could legitimately support a reverse inequality. -/
structure ReversePoincareExtraStructure where
  zero_mode_removed : Prop
  annular_support_or_spectral_gap : Prop
  mean_zero_or_boundary_condition : Prop
  reverse_estimate_proved : Prop

inductive LowDirectAbsorptionRouteStatus where
  | openWithoutExtraStructure
  | provedWithCertifiedSpectralGap
  | refutedForProposedHypotheses
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
