/-!
NS-FORCING-001 / Sobolev L6 block.

This file proves the compact-support H1 -> L6 estimate for the concrete
three-dimensional space using Mathlib's Gagliardo--Nirenberg--Sobolev theorem.

No Navier--Stokes closure assumption or signed-gain assumption occurs here.
This block is intended as a pure analytic input to the later CZ frontier.
-/

import open_math.ActualNSToSignedGainCore.P1_ConcreteObservables
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

noncomputable section

open Set MeasureTheory
open scoped ENNReal ContDiff

namespace NSProducerFirst.P1Concrete

/-- The fixed Sobolev constant for R^3 at p=2. -/
def sobolevL6Constant : ℝ :=
  (eLpNormLESNormFDerivOfEqInnerConst
    (volume : Measure Space) (2 : ℝ≥0) : ℝ)

theorem sobolevL6Constant_nonneg : 0 ≤ sobolevL6Constant := by
  unfold sobolevL6Constant
  exact NNReal.coe_nonneg _

/--
Compact-support homogeneous Sobolev in physical dimension three:
  ||w||_6 <= C_S ||Dw||_2.
-/
theorem compact_sobolev_L6
    {w : Space → Space}
    (hw : ContDiff ℝ 1 w)
    (hcompact : HasCompactSupport w) :
    eLpNorm w 6 (volume : Measure Space) ≤
      (eLpNormLESNormFDerivOfEqInnerConst
        (volume : Measure Space) (2 : ℝ≥0) : ℝ≥0∞) *
      eLpNorm (fderiv ℝ w) 2 (volume : Measure Space) := by
  have hdim : Module.finrank ℝ Space = 3 := by
    simp [Space]
  exact eLpNorm_le_eLpNorm_fderiv_of_eq_inner
    (volume : Measure Space)
    hw
    hcompact
    (p := (2 : ℝ≥0))
    (p' := (6 : ℝ≥0))
    (by norm_num)
    (by rw [hdim]; norm_num)
    (by rw [hdim]; norm_num)

/--
Real-valued form when the derivative is genuinely L2.
-/
theorem compact_sobolev_L6_toReal
    {w : Space → Space}
    (hw : ContDiff ℝ 1 w)
    (hcompact : HasCompactSupport w)
    (hDw2 : MemLp (fderiv ℝ w) 2 (volume : Measure Space)) :
    (eLpNorm w 6 (volume : Measure Space)).toReal ≤
      sobolevL6Constant *
        (eLpNorm (fderiv ℝ w) 2 (volume : Measure Space)).toReal := by
  have h := compact_sobolev_L6 hw hcompact
  have hfinite :
      (eLpNormLESNormFDerivOfEqInnerConst
        (volume : Measure Space) (2 : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ w) 2 (volume : Measure Space) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hDw2.eLpNorm_lt_top).ne
  simpa [sobolevL6Constant, ENNReal.toReal_mul] using
    ENNReal.toReal_mono hfinite h

end NSProducerFirst.P1Concrete
