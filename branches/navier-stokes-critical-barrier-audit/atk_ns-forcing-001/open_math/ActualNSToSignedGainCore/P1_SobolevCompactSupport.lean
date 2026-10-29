import open_math.ActualNSToSignedGainCore.P1_ConcreteObservables
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
NS-FORCING-001 / concrete compact-support Sobolev step.

This module closes the Mathlib-supported W^{1,2}(R^3) -> L^6(R^3)
step for a concrete vorticity slice when compact support and C1 regularity
are genuinely available.  It does not assert compact support for arbitrary
Navier--Stokes states.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

/-- Exact Mathlib Sobolev estimate at the physical exponents p=2, p'=6
in dimension three. -/
theorem vorticity_eLpNorm_six_le_fderiv_two_of_compactSupport
    (u : VelocityField) (t : ℝ)
    (hcont : ContDiff ℝ 1 (vorticity u t))
    (hsupp : HasCompactSupport (vorticity u t)) :
    eLpNorm (vorticity u t) 6 (volume : Measure Space) ≤
      eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure Space) 2 *
        eLpNorm (fderiv ℝ (vorticity u t)) 2
          (volume : Measure Space) := by
  have h :=
    MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner
      (μ := (volume : Measure Space))
      hcont hsupp
      (p := (2 : NNReal)) (p' := (6 : NNReal))
      (by norm_num) (by simp [Space]) (by norm_num [Space])
  simpa using h

/-- Packaging of the two genuinely analytic premises required to apply the
compact-support Sobolev theorem to one physical time slice. -/
structure CompactSupportSobolevSlice
    (u : VelocityField) (t : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 (vorticity u t)
  compactSupport : HasCompactSupport (vorticity u t)

theorem CompactSupportSobolevSlice.sobolev
    {u : VelocityField} {t : ℝ}
    (h : CompactSupportSobolevSlice u t) :
    eLpNorm (vorticity u t) 6 (volume : Measure Space) ≤
      eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure Space) 2 *
        eLpNorm (fderiv ℝ (vorticity u t)) 2
          (volume : Measure Space) :=
  vorticity_eLpNorm_six_le_fderiv_two_of_compactSupport
    u t h.contDiff h.compactSupport

#print axioms NSProducerFirst.P1Concrete.vorticity_eLpNorm_six_le_fderiv_two_of_compactSupport
#print axioms NSProducerFirst.P1Concrete.CompactSupportSobolevSlice.sobolev

end NSProducerFirst.P1Concrete
