import CriticalBarrier.K1aFrechet
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace CriticalBarrier.K1aExactFrechetProducer

open CriticalBarrier.K1aVectorKernel
open CriticalBarrier.K1aChainRule
open CriticalBarrier.K1aFrechet

theorem inverseRadiusDerivativeMap
    {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (-(r eps w ^ 2)⁻¹)).comp
      ((1 / (2 * r eps w)) • (2 • innerSL ℝ w)))
      =
    (-(r eps w ^ 3)⁻¹) • innerSL ℝ w := by
  apply ContinuousLinearMap.ext
  intro v
  have hr0 : r eps w ≠ 0 := r_ne_zero heps w
  simp
  rw [show (r eps w ^ 2)⁻¹ = (r eps w)⁻¹ ^ 2 by rw [inv_pow]]
  rw [show (r eps w ^ 3)⁻¹ = (r eps w)⁻¹ ^ 3 by rw [inv_pow]]
  rw [← Finset.sum_mul]
  field_simp [hr0]
  ring_nf

theorem productDerivativeMap
    {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    (r eps w)⁻¹ • (1 : Vec3 →L[ℝ] Vec3) +
        (((-(r eps w ^ 3)⁻¹) • innerSL ℝ w).smulRight w)
      =
    DxiCLM eps w := by
  apply ContinuousLinearMap.ext
  intro v
  rw [DxiCLM_apply]
  simp [DxiCandidate, sub_eq_add_neg]

/-- Exact Fréchet derivative of the regularized direction map
    xi_eps(w) = w / sqrt(||w||^2 + eps^2), for eps > 0. -/
theorem xi_hasFDerivAt_DxiCLM
    {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    HasFDerivAt (xi eps) (DxiCLM eps w) w := by
  have hq :
      HasFDerivAt
        (fun y : Vec3 => ‖y‖ ^ 2 + eps ^ 2)
        (2 • innerSL ℝ w) w := by
    simpa using (hasFDerivAt_id w).norm_sq.add_const (eps ^ 2)
  have hq_ne :
      ‖w‖ ^ 2 + eps ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ‖w‖, sq_pos_of_pos heps]
  have hr :
      HasFDerivAt
        (fun y : Vec3 => Real.sqrt (‖y‖ ^ 2 + eps ^ 2))
        ((1 / (2 * r eps w)) • (2 • innerSL ℝ w)) w := by
    simpa [r] using hq.sqrt hq_ne
  have hr_ne : r eps w ≠ 0 := r_ne_zero heps w
  have hinv0 := (hasFDerivAt_inv hr_ne).comp w hr
  rw [inverseRadiusDerivativeMap heps w] at hinv0
  have hid : HasFDerivAt (fun y : Vec3 => y) (1 : Vec3 →L[ℝ] Vec3) w :=
    hasFDerivAt_id w
  have hprod0 := hinv0.smul hid
  have hprod :
      HasFDerivAt (fun y => (r eps y)⁻¹ • y)
        ((r eps w)⁻¹ • (1 : Vec3 →L[ℝ] Vec3) +
          (((-(r eps w ^ 3)⁻¹) • innerSL ℝ w).smulRight w)) w := by
    simpa [Function.comp_apply] using hprod0
  rw [productDerivativeMap heps w] at hprod
  simpa [xi] using hprod

theorem xiFrechetTarget_closed
    {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    XiFrechetTarget eps w :=
  xi_hasFDerivAt_DxiCLM heps w

theorem exactDerivativeStatement_closed
    {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    ExactDerivativeStatement eps w :=
  exactDerivative_from_target (xiFrechetTarget_closed heps w)

/-- Forward chain-rule corollary: once the input path has a derivative,
    the exact Frechet inhabitant gives the time derivative of xi_eps. -/
theorem xi_chainRule_of_hasDerivAt
    {eps : ℝ} (heps : 0 < eps)
    {w : ℝ → Vec3} {t : ℝ} {w' : Vec3}
    (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => xi eps (w s))
      (DxiCandidate eps (w t) w') t := by
  have hxi :
      HasFDerivAt (xi eps) (DxiCLM eps (w t)) (w t) :=
    xi_hasFDerivAt_DxiCLM heps (w t)
  have hcomp := hxi.comp_hasDerivAt t hw
  simpa [DxiCLM_apply] using hcomp

/-- The named ChainRuleStatement follows whenever w is differentiable at t. -/
theorem chainRuleStatement_closed_of_differentiableAt
    {eps : ℝ} (heps : 0 < eps)
    {w : ℝ → Vec3} {t : ℝ}
    (hw : DifferentiableAt ℝ w t) :
    ChainRuleStatement eps w t := by
  have h := xi_chainRule_of_hasDerivAt heps hw.hasDerivAt
  simpa [ChainRuleStatement] using h

#print axioms CriticalBarrier.K1aExactFrechetProducer.inverseRadiusDerivativeMap
#print axioms CriticalBarrier.K1aExactFrechetProducer.productDerivativeMap
#print axioms CriticalBarrier.K1aExactFrechetProducer.xi_hasFDerivAt_DxiCLM
#print axioms CriticalBarrier.K1aExactFrechetProducer.xiFrechetTarget_closed
#print axioms CriticalBarrier.K1aExactFrechetProducer.exactDerivativeStatement_closed

end CriticalBarrier.K1aExactFrechetProducer

-- ATK verification trigger v4
