import Mathlib
import MPrivate.NS.ThirdCoefficient.EightTermSignedGrouping

namespace MPrivate.NS.ThirdCoefficient

/-!
# SixBlockSignIndefiniteness

Frequency labels alone do not fix the sign of any of the six scalar spectral
interaction classes.  Each block admits both positive and negative examples.
This is an adversarial sign certificate: actual PDE structure may impose extra
relations, but those relations must be proved rather than inferred from labels.
-/

/-- LLL admits both signs. -/
theorem VLLL_sign_indefinite :
    (∃ sL wL : ℝ, 0 < VLLL sL wL) ∧
    (∃ sL wL : ℝ, VLLL sL wL < 0) := by
  constructor
  · exact ⟨1, 1, by norm_num [VLLL]⟩
  · exact ⟨-1, 1, by norm_num [VLLL]⟩

/-- LLH pair admits both signs. -/
theorem VLLHpair_sign_indefinite :
    (∃ sL wL wH : ℝ, 0 < VLLHpair sL wL wH) ∧
    (∃ sL wL wH : ℝ, VLLHpair sL wL wH < 0) := by
  constructor
  · exact ⟨1, 1, 1, by norm_num [VLLHpair]⟩
  · exact ⟨-1, 1, 1, by norm_num [VLLHpair]⟩

/-- LHH admits both signs. -/
theorem VLHH_sign_indefinite :
    (∃ sL wH : ℝ, 0 < VLHH sL wH) ∧
    (∃ sL wH : ℝ, VLHH sL wH < 0) := by
  constructor
  · exact ⟨1, 1, by norm_num [VLHH]⟩
  · exact ⟨-1, 1, by norm_num [VLHH]⟩

/-- HLL admits both signs. -/
theorem VHLL_sign_indefinite :
    (∃ sH wL : ℝ, 0 < VHLL sH wL) ∧
    (∃ sH wL : ℝ, VHLL sH wL < 0) := by
  constructor
  · exact ⟨1, 1, by norm_num [VHLL]⟩
  · exact ⟨-1, 1, by norm_num [VHLL]⟩

/-- HLH pair admits both signs. -/
theorem VHLHpair_sign_indefinite :
    (∃ sH wL wH : ℝ, 0 < VHLHpair sH wL wH) ∧
    (∃ sH wL wH : ℝ, VHLHpair sH wL wH < 0) := by
  constructor
  · exact ⟨1, 1, 1, by norm_num [VHLHpair]⟩
  · exact ⟨-1, 1, 1, by norm_num [VHLHpair]⟩

/-- HHH admits both signs. -/
theorem VHHH_sign_indefinite :
    (∃ sH wH : ℝ, 0 < VHHH sH wH) ∧
    (∃ sH wH : ℝ, VHHH sH wH < 0) := by
  constructor
  · exact ⟨1, 1, by norm_num [VHHH]⟩
  · exact ⟨-1, 1, by norm_num [VHHH]⟩

/-- Audit conclusion: no spectral class is `freeBySign` from its label alone. -/
def FrequencyLabelFreeBySignStatus : String :=
  "FORMAL_REFUTED_FOR_ALL_SIX_SCALAR_BLOCK_CLASSES"

end MPrivate.NS.ThirdCoefficient
