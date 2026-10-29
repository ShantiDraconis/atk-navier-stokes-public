import open_math.ActualNSToSignedGainCore.P1_ConcreteObservables
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
NS-FORCING-001 / minimal whole-space cutoffs for the P1 Sobolev passage.

Ported in minimal form from openai/NavierStokesAndEuler's
NavierStokes/R3/ComparisonCutoffs.lean.
No axiom, sorry, or Navier--Stokes closure assumption.
-/

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace NSProducerFirst.P1Concrete

noncomputable def p1BaseBump : ContDiffBump (0 : Space) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def p1BaseCutoff (x : Space) : ℝ := p1BaseBump x

def p1Cutoff (R : ℝ) (x : Space) : ℝ :=
  p1BaseCutoff (R⁻¹ • x)

theorem p1BaseCutoff_smooth : ContDiff ℝ ∞ p1BaseCutoff :=
  p1BaseBump.contDiff

theorem p1Cutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (p1Cutoff R) :=
  p1BaseCutoff_smooth.comp (by fun_prop)

theorem p1Cutoff_nonneg (R : ℝ) (x : Space) :
    0 ≤ p1Cutoff R x :=
  p1BaseBump.nonneg

theorem p1Cutoff_le_one (R : ℝ) (x : Space) :
    p1Cutoff R x ≤ 1 :=
  p1BaseBump.le_one

theorem p1_norm_scaled {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖R⁻¹ • x‖ = ‖x‖ / R := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_eq_inv_mul]

theorem p1Cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Space}
    (hx : ‖x‖ ≤ R) :
    p1Cutoff R x = 1 := by
  apply p1BaseBump.one_of_mem_closedBall
  simpa [p1Cutoff, p1BaseCutoff, p1BaseBump, mem_closedBall, dist_zero_right,
    p1_norm_scaled hR, div_le_one hR] using hx

theorem p1Cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Space}
    (hx : 2 * R ≤ ‖x‖) :
    p1Cutoff R x = 0 := by
  apply p1BaseBump.zero_of_le_dist
  simpa [p1Cutoff, p1BaseCutoff, p1BaseBump, dist_zero_right,
    p1_norm_scaled hR, le_div_iff₀ hR] using hx

theorem p1Cutoff_support_subset {R : ℝ} (hR : 0 < R) :
    Function.support (p1Cutoff R) ⊆ ball (0 : Space) (2 * R) := by
  intro x hx
  by_contra h
  apply hx
  exact p1Cutoff_eq_zero hR
    (by simpa [mem_ball, dist_zero_right, not_lt] using h)

theorem p1Cutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (p1Cutoff R) := by
  have hsub :
      tsupport (p1Cutoff R) ⊆ closedBall (0 : Space) (2 * R) :=
    closure_minimal
      ((p1Cutoff_support_subset hR).trans ball_subset_closedBall)
      isClosed_closedBall
  exact (isCompact_closedBall (0 : Space) (2 * R)).of_isClosed_subset
    isClosed_closure hsub

private theorem p1_exists_derivative_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : Space, ‖fderiv ℝ p1BaseCutoff x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (p1BaseBump.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
      (p1BaseCutoff_smooth.continuous_fderiv (by simp))
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hC x).trans (le_max_right _ _)⟩

def p1DerivativeConstant : ℝ :=
  Classical.choose p1_exists_derivative_bound

theorem p1DerivativeConstant_pos : 0 < p1DerivativeConstant :=
  (Classical.choose_spec p1_exists_derivative_bound).1

theorem p1BaseCutoff_fderiv_le (x : Space) :
    ‖fderiv ℝ p1BaseCutoff x‖ ≤ p1DerivativeConstant :=
  (Classical.choose_spec p1_exists_derivative_bound).2 x

private def p1Dilation (R : ℝ) : Space →L[ℝ] Space :=
  R⁻¹ • ContinuousLinearMap.id ℝ Space

private theorem p1_norm_dilation_le {R : ℝ} (hR : 0 < R) :
    ‖p1Dilation R‖ ≤ R⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hR.le)
  intro x
  change ‖R⁻¹ • x‖ ≤ R⁻¹ * ‖x‖
  rw [p1_norm_scaled hR, div_eq_inv_mul]

theorem p1Cutoff_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (p1Cutoff R) x‖ ≤ p1DerivativeConstant / R := by
  have hfun : p1Cutoff R = p1BaseCutoff ∘ p1Dilation R := by
    funext y
    rfl
  have hbase :
      HasFDerivAt p1BaseCutoff
        (fderiv ℝ p1BaseCutoff (p1Dilation R x))
        (p1Dilation R x) :=
    ((p1BaseCutoff_smooth.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hdil :
      HasFDerivAt (fun y : Space => p1Dilation R y) (p1Dilation R) x :=
    (p1Dilation R).hasFDerivAt
  have hcomp := hbase.comp x hdil
  rw [hfun, hcomp.fderiv]
  calc
    ‖(fderiv ℝ p1BaseCutoff (p1Dilation R x)).comp (p1Dilation R)‖
        ≤ ‖fderiv ℝ p1BaseCutoff (p1Dilation R x)‖ * ‖p1Dilation R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ p1DerivativeConstant * R⁻¹ := by
      exact mul_le_mul
        (p1BaseCutoff_fderiv_le _)
        (p1_norm_dilation_le hR)
        (norm_nonneg _) p1DerivativeConstant_pos.le
    _ = p1DerivativeConstant / R := by
      rw [div_eq_mul_inv]

theorem p1_eventually_cutoff_eq_one (x : Space) :
    ∀ᶠ n : ℕ in Filter.atTop, p1Cutoff (n : ℝ) x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hNn : N ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  apply p1Cutoff_eq_one hnpos
  exact hN.trans (by exact_mod_cast hNn)

#print axioms NSProducerFirst.P1Concrete.p1Cutoff_fderiv_le
#print axioms NSProducerFirst.P1Concrete.p1_eventually_cutoff_eq_one

end NSProducerFirst.P1Concrete
