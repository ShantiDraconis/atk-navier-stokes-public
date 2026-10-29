import open_math.ActualNSToSignedGainCore.P1_ConcreteObservables
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
NS-FORCING-001 / generic L2-L6 -> L3 interpolation on physical R^3.

Minimal port of the audited interpolation argument used in
openai/NavierStokesAndEuler.  Depends only on Mathlib plus the concrete Space
already defined for P1.  No sorry/admit/axiom.
-/


noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NSProducerFirst.P1Concrete

/-- Real-valued Lp seminorm on physical R^3. -/
def realLpNorm {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (f : Space → E) : ℝ :=
  (eLpNorm f p (volume : Measure Space)).toReal

/--
Hölder interpolation specialized to the midpoint exponents 2,6 -> 3.
-/
theorem eLpNorm_three_le
    {E : Type*} [NormedAddCommGroup E]
    {f : Space → E}
    (h2m : AEStronglyMeasurable f (volume : Measure Space)) :
    eLpNorm f 3 (volume : Measure Space) ≤
      eLpNorm f 2 (volume : Measure Space) ^ (1 / 2 : ℝ) *
      eLpNorm f 6 (volume : Measure Space) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
      eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
      eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
  calc
    eLpNorm' f 3 (volume : Measure Space)
        ≤ eLpNorm'
            (fun x : Space =>
              ‖f x‖ ^ (1 / 2 : ℝ) * ‖f x‖ ^ (1 / 2 : ℝ))
            3 (volume : Measure Space) := by
          apply eLpNorm'_mono_ae (by norm_num)
          filter_upwards [] with x
          by_cases hzero : ‖f x‖ = 0
          · simp [hzero]
          · have hpos : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
            rw [← Real.rpow_add hpos]
            norm_num
    _ ≤ eLpNorm' (fun x : Space => ‖f x‖ ^ (1 / 2 : ℝ)) 4
          (volume : Measure Space) *
        eLpNorm' (fun x : Space => ‖f x‖ ^ (1 / 2 : ℝ)) 12
          (volume : Measure Space) := by
          simpa using
            eLpNorm'_le_eLpNorm'_mul_eLpNorm'
              (h2m.norm.aemeasurable.pow_const (1 / 2 : ℝ)).aestronglyMeasurable
              (h2m.norm.aemeasurable.pow_const (1 / 2 : ℝ)).aestronglyMeasurable
              (fun x y : ℝ => x * y) 1
              (Filter.Eventually.of_forall fun x => by simp [nnnorm_mul])
              (by norm_num : 0 < (3 : ℝ))
              (by norm_num : (3 : ℝ) < 4)
              (by norm_num : 1 / (3 : ℝ) = 1 / 4 + 1 / 12)
    _ = eLpNorm' f 2 (volume : Measure Space) ^ (1 / 2 : ℝ) *
        eLpNorm' f 6 (volume : Measure Space) ^ (1 / 2 : ℝ) := by
          rw [eLpNorm'_norm_rpow _ _ _ (by norm_num : 0 < (1 / 2 : ℝ)),
              eLpNorm'_norm_rpow _ _ _ (by norm_num : 0 < (1 / 2 : ℝ))]
          norm_num

/--
Membership and real-norm interpolation:
  ||f||_3 <= ||f||_2^(1/2) ||f||_6^(1/2).
-/
theorem memLp_three_and_norm_le
    {E : Type*} [NormedAddCommGroup E]
    {f : Space → E}
    (h2 : MemLp f 2 (volume : Measure Space))
    (h6 : MemLp f 6 (volume : Measure Space)) :
    MemLp f 3 (volume : Measure Space) ∧
      realLpNorm 3 f ≤
        realLpNorm 2 f ^ (1 / 2 : ℝ) *
        realLpNorm 6 f ^ (1 / 2 : ℝ) := by
  have hbound := eLpNorm_three_le h2.1
  have hfinite :
      eLpNorm f 2 (volume : Measure Space) ^ (1 / 2 : ℝ) *
        eLpNorm f 6 (volume : Measure Space) ^ (1 / 2 : ℝ) < ∞ :=
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h6.eLpNorm_ne_top)
  refine ⟨⟨h2.1, hbound.trans_lt hfinite⟩, ?_⟩
  unfold realLpNorm
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow] using
    ENNReal.toReal_mono hfinite.ne hbound

end NSProducerFirst.P1Concrete
