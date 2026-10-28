import Mathlib

namespace NSProducerFirst

/-!
Counter-audit for the legacy `formal/G1/WeightedLow.lean` constants.

The legacy route fixes

  C_abs = 0.6
  C_Young = 50
  gamma_effective = 1 - 2 * C_abs^2 * C_Young

while its absorption record requires a strictly positive gamma bounded above by
gamma_effective.  The arithmetic below shows that this constraint set is empty.

This file does not modify the legacy source and does not construct the current
terminal producer `ActualNSToSignedGain`.
-/

def legacyCAbs : ℝ := 0.6
def legacyCYoung : ℝ := 50

def legacyGammaEffective : ℝ :=
  1 - 2 * legacyCAbs ^ 2 * legacyCYoung

theorem legacyGammaEffective_eq_neg35 :
    legacyGammaEffective = -35 := by
  norm_num [legacyGammaEffective, legacyCAbs, legacyCYoung]

structure LegacyWeightedAbsorptionConstraints where
  gamma : ℝ
  gamma_pos : 0 < gamma
  gamma_from_constant : gamma ≤ legacyGammaEffective

theorem legacy_weighted_absorption_constraints_uninhabited :
    ¬ Nonempty LegacyWeightedAbsorptionConstraints := by
  rintro ⟨h⟩
  have hupper : h.gamma ≤ -35 := by
    simpa [legacyGammaEffective_eq_neg35] using h.gamma_from_constant
  linarith [h.gamma_pos, hupper]

/-- Exact arithmetic verdict: with the frozen legacy constants there is no
strictly positive absorption coefficient satisfying the advertised upper
bound. -/
theorem no_positive_gamma_below_legacy_effective :
    ¬ ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ legacyGammaEffective := by
  rintro ⟨gamma, hpos, hupper⟩
  rw [legacyGammaEffective_eq_neg35] at hupper
  linarith

#print axioms NSProducerFirst.legacyGammaEffective_eq_neg35
#print axioms NSProducerFirst.legacy_weighted_absorption_constraints_uninhabited
#print axioms NSProducerFirst.no_positive_gamma_below_legacy_effective

end NSProducerFirst
