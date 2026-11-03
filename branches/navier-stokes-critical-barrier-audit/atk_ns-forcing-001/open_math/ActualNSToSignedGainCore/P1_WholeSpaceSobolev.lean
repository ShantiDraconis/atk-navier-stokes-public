import open_math.ActualNSToSignedGainCore.P1_WholeSpaceCutoff
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
NS-FORCING-001 / whole-space homogeneous Sobolev without compact support.

Ported from openai/NavierStokesAndEuler's SmoothSobolevL6 argument and adapted
to the P1 concrete Space.  No axiom, sorry, or endpoint regularity assumption.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace NSProducerFirst.P1Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem p1_norm_fderiv_cutoff_smul_le
    {f : Space → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fun y => p1Cutoff R y • f y) x‖ ≤
      ‖fderiv ℝ f x‖ + (p1DerivativeConstant / R) * ‖f x‖ := by
  have hfd :=
    fderiv_smul
      ((p1Cutoff_smooth R).differentiable (by simp) x)
      (hf.differentiable (by simp) x)
  change
    fderiv ℝ (fun y => p1Cutoff R y • f y) x =
      p1Cutoff R x • fderiv ℝ f x +
        (fderiv ℝ (p1Cutoff R) x).smulRight (f x) at hfd
  rw [hfd]
  calc
    ‖p1Cutoff R x • fderiv ℝ f x +
        (fderiv ℝ (p1Cutoff R) x).smulRight (f x)‖
        ≤ ‖p1Cutoff R x • fderiv ℝ f x‖ +
          ‖(fderiv ℝ (p1Cutoff R) x).smulRight (f x)‖ := norm_add_le _ _
    _ = p1Cutoff R x * ‖fderiv ℝ f x‖ +
        ‖fderiv ℝ (p1Cutoff R) x‖ * ‖f x‖ := by
      rw [_root_.norm_smul (p1Cutoff R x) (fderiv ℝ f x),
        Real.norm_eq_abs, abs_of_nonneg (p1Cutoff_nonneg R x),
        ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ 1 * ‖fderiv ℝ f x‖ +
        (p1DerivativeConstant / R) * ‖f x‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (p1Cutoff_le_one R x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (p1Cutoff_fderiv_le hR x) (norm_nonneg _))
    _ = ‖fderiv ℝ f x‖ + (p1DerivativeConstant / R) * ‖f x‖ := by
      rw [one_mul]

theorem p1_eLpNorm_fderiv_cutoff_smul_le
    {f : Space → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) :
    eLpNorm (fderiv ℝ (fun y => p1Cutoff R y • f y)) 2 volume ≤
      eLpNorm (fderiv ℝ f) 2 volume +
        ENNReal.ofReal (p1DerivativeConstant / R) * eLpNorm f 2 volume := by
  calc
    eLpNorm (fderiv ℝ (fun y => p1Cutoff R y • f y)) 2 volume
        ≤ eLpNorm (fun x => ‖fderiv ℝ f x‖ +
          (p1DerivativeConstant / R) * ‖f x‖) 2 volume :=
      eLpNorm_mono_real (p1_norm_fderiv_cutoff_smul_le hf hR)
    _ ≤ eLpNorm (fun x => ‖fderiv ℝ f x‖) 2 volume +
        eLpNorm (fun x => (p1DerivativeConstant / R) * ‖f x‖) 2 volume :=
      eLpNorm_add_le
        (hf.continuous_fderiv (by simp)).norm.aestronglyMeasurable
        (continuous_const.mul hf.continuous.norm).aestronglyMeasurable
        (by norm_num)
    _ = eLpNorm (fderiv ℝ f) 2 volume +
        ENNReal.ofReal (p1DerivativeConstant / R) * eLpNorm f 2 volume := by
      rw [eLpNorm_norm]
      change _ + eLpNorm ((p1DerivativeConstant / R) •
        (fun x => ‖f x‖)) 2 volume = _
      rw [eLpNorm_const_smul, eLpNorm_norm,
        Real.enorm_eq_ofReal (div_nonneg p1DerivativeConstant_pos.le hR.le)]

/-- Homogeneous H1 -> L6 on R3 without a compact-support assumption. -/
theorem p1_smooth_eLpNorm_six_le
    {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) :
    eLpNorm f 6 volume ≤
      (eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure Space) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume := by
  let C : ℝ≥0∞ :=
    eLpNormLESNormFDerivOfEqInnerConst
      (volume : Measure Space) 2
  let D : ℝ≥0∞ := eLpNorm (fderiv ℝ f) 2 volume
  let M : ℝ≥0∞ := eLpNorm f 2 volume
  let u : ℕ → Space → E := fun n x => p1Cutoff (n : ℝ) x • f x
  have hu (n : ℕ) : ContDiff ℝ 1 (u n) :=
    ((p1Cutoff_smooth (n : ℝ)).of_le (by simp)).smul hf
  have hpointwise (x : Space) :
      Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [p1_eventually_cutoff_eq_one x] with n hn
    simp only [u, hn, one_smul]
  have hfatou :
      eLpNorm f 6 volume ≤
        atTop.liminf (fun n => eLpNorm (u n) 6 volume) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (hu n).continuous.aestronglyMeasurable) f
      (Filter.Eventually.of_forall hpointwise)
  have hn_dim : Module.finrank ℝ Space = 3 := by
    simp [Space]
  have hbound : ∀ᶠ n : ℕ in atTop,
      eLpNorm (u n) 6 volume ≤
        C * (D +
          ENNReal.ofReal (p1DerivativeConstant / (n : ℝ)) * M) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hcompact : HasCompactSupport (u n) :=
      (p1Cutoff_hasCompactSupport hnR).smul_right
    have hSob :=
      eLpNorm_le_eLpNorm_fderiv_of_eq_inner
        (μ := (volume : Measure Space))
        (hu n) hcompact
        (p := (2 : ℝ≥0)) (p' := (6 : ℝ≥0))
        (by norm_num)
        (by rw [hn_dim]; norm_num)
        (by rw [hn_dim]; norm_num)
    have hSob' :
        eLpNorm (u n) 6 volume ≤
          C * eLpNorm (fderiv ℝ (u n)) 2 volume := by
      simpa [C] using hSob
    exact hSob'.trans
      (mul_le_mul_of_nonneg_left
        (p1_eLpNorm_fderiv_cutoff_smul_le hf hnR)
        (by positivity))
  have herr :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (p1DerivativeConstant / (n : ℝ)) * M)
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_ofReal
        (tendsto_const_div_atTop_nhds_zero_nat p1DerivativeConstant))
      (Or.inr h2.eLpNorm_ne_top)
  have hsum :
      Tendsto
        (fun n : ℕ =>
          D + ENNReal.ofReal (p1DerivativeConstant / (n : ℝ)) * M)
        atTop (𝓝 (D + 0)) :=
    tendsto_const_nhds.add herr
  have hlimit :
      Tendsto
        (fun n : ℕ =>
          C * (D + ENNReal.ofReal
            (p1DerivativeConstant / (n : ℝ)) * M))
        atTop (𝓝 (C * D)) := by
    simpa only [add_zero] using
      ENNReal.Tendsto.const_mul hsum
        (Or.inr
          (show C ≠ (⊤ : ℝ≥0∞) from ENNReal.coe_ne_top))
  exact hfatou.trans
    ((Filter.liminf_le_liminf hbound).trans_eq hlimit.liminf_eq)

theorem p1_smooth_memLp_six
    {f : Space → E}
    (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume)
    (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    MemLp f 6 volume := by
  refine ⟨hf.continuous.aestronglyMeasurable,
    (p1_smooth_eLpNorm_six_le hf h2).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hD2.2



/-- Real-valued whole-space Sobolev inequality, used by the H1-to-L3
compression below. -/
theorem p1_smooth_eLpNorm_six_toReal_le
    {f : Space → E}
    (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume)
    (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    (eLpNorm f 6 volume).toReal ≤
      (eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure Space) 2 : ℝ) *
        (eLpNorm (fderiv ℝ f) 2 volume).toReal := by
  have hfinite :
      (eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure Space) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hD2.2).ne
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using
    ENNReal.toReal_mono hfinite (p1_smooth_eLpNorm_six_le hf h2)

#print axioms NSProducerFirst.P1Concrete.p1_smooth_eLpNorm_six_le
#print axioms NSProducerFirst.P1Concrete.p1_smooth_memLp_six
#print axioms NSProducerFirst.P1Concrete.p1_smooth_eLpNorm_six_toReal_le

end NSProducerFirst.P1Concrete
