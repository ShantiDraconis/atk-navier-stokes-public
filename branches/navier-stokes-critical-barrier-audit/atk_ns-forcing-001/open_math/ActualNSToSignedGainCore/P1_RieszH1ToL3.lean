import open_math.ActualNSToSignedGainCore.P1_LpInterpolation
import open_math.ActualNSToSignedGainCore.P1_WholeSpaceSobolev

/-!
NS-FORCING-001 / H1-to-L3 compression.

This theorem packages only already-proved functional analysis:
whole-space H1 -> L6 plus L2/L6 -> L3 interpolation.

It does not assume or prove any Navier--Stokes endpoint theorem.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

/-- Any smooth R3 field with finite L2 value and finite L2 derivative lies in L3.
The quantitative bound is exactly the geometric mean of the L2 norm and the
Sobolev-controlled L6 norm. -/
theorem h1_to_l3_compression
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Space → E}
    (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume)
    (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    MemLp f 3 volume ∧
      realLpNorm 3 f ≤
        realLpNorm 2 f ^ (1 / 2 : ℝ) *
          (((eLpNormLESNormFDerivOfEqInnerConst
              (volume : Measure Space) 2 : ℝ) *
            realLpNorm 2 (fderiv ℝ f)) ^ (1 / 2 : ℝ)) := by
  have h6 : MemLp f 6 volume :=
    p1_smooth_memLp_six hf h2 hD2
  obtain ⟨h3, h36⟩ := memLp_three_and_norm_le h2 h6
  refine ⟨h3, h36.trans ?_⟩
  have hSob :=
    p1_smooth_eLpNorm_six_toReal_le hf h2 hD2
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hpow :=
    Real.rpow_le_rpow
      (show 0 ≤ realLpNorm 6 f by exact ENNReal.toReal_nonneg)
      hSob hhalf
  gcongr

/-- Kernel-forcing form for an operator output g=T f.  To get the L3 output,
it is enough to supply an L2 output bound and an L2 derivative bound.
No general L3 Calderon--Zygmund theorem is required. -/
theorem operator_output_l3_of_l2_and_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : Space → E}
    (hg : ContDiff ℝ 1 g)
    (hg2 : MemLp g 2 volume)
    (hgD2 : MemLp (fderiv ℝ g) 2 volume)
    (hf2 : MemLp f 2 volume)
    (hfD2 : MemLp (fderiv ℝ f) 2 volume)
    (h0 : realLpNorm 2 g ≤ realLpNorm 2 f)
    (A : ℝ) (hA : 0 ≤ A)
    (h1 : realLpNorm 2 (fderiv ℝ g) ≤
      A * realLpNorm 2 (fderiv ℝ f)) :
    MemLp g 3 volume ∧
      realLpNorm 3 g ≤
        realLpNorm 2 f ^ (1 / 2 : ℝ) *
          (((eLpNormLESNormFDerivOfEqInnerConst
              (volume : Measure Space) 2 : ℝ) *
            (A * realLpNorm 2 (fderiv ℝ f))) ^ (1 / 2 : ℝ)) := by
  obtain ⟨hg3, hb⟩ := h1_to_l3_compression hg hg2 hgD2
  refine ⟨hg3, hb.trans ?_⟩
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have h0pow :=
    Real.rpow_le_rpow
      (show 0 ≤ realLpNorm 2 g by exact ENNReal.toReal_nonneg)
      h0 hhalf
  have hSobC :
      0 ≤ (eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure Space) 2 : ℝ) := by positivity
  have h1' :
      (eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure Space) 2 : ℝ) *
          realLpNorm 2 (fderiv ℝ g) ≤
        (eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure Space) 2 : ℝ) *
          (A * realLpNorm 2 (fderiv ℝ f)) :=
    mul_le_mul_of_nonneg_left h1 hSobC
  have h1pow :=
    Real.rpow_le_rpow
      (mul_nonneg hSobC ENNReal.toReal_nonneg)
      h1' hhalf
  exact mul_le_mul h0pow h1pow
    (Real.rpow_nonneg (realLpNorm 2 g) _)
    (Real.rpow_nonneg _ _)



/-- Exact Riesz-test numerical specialization observed in the formal corpus:
L2 contraction with derivative L2 amplification at most 3.  Once the concrete
Biot--Savart/Riesz representation supplies these two inequalities, L3 follows. -/
theorem riesz_three_l3_of_unit_l2_and_triple_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : Space → E}
    (hg : ContDiff ℝ 1 g)
    (hg2 : MemLp g 2 volume)
    (hgD2 : MemLp (fderiv ℝ g) 2 volume)
    (hf2 : MemLp f 2 volume)
    (hfD2 : MemLp (fderiv ℝ f) 2 volume)
    (hL2 : realLpNorm 2 g ≤ realLpNorm 2 f)
    (hD2 : realLpNorm 2 (fderiv ℝ g) ≤
      3 * realLpNorm 2 (fderiv ℝ f)) :
    MemLp g 3 volume ∧
      realLpNorm 3 g ≤
        realLpNorm 2 f ^ (1 / 2 : ℝ) *
          (((eLpNormLESNormFDerivOfEqInnerConst
              (volume : Measure Space) 2 : ℝ) *
            (3 * realLpNorm 2 (fderiv ℝ f))) ^ (1 / 2 : ℝ)) := by
  exact operator_output_l3_of_l2_and_derivative
    hg hg2 hgD2 hf2 hfD2 hL2 3 (by norm_num) hD2

#print axioms NSProducerFirst.P1Concrete.h1_to_l3_compression
#print axioms NSProducerFirst.P1Concrete.operator_output_l3_of_l2_and_derivative
#print axioms NSProducerFirst.P1Concrete.riesz_three_l3_of_unit_l2_and_triple_derivative

end NSProducerFirst.P1Concrete
