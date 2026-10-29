import Mathlib

namespace CriticalBarrier.K1aVectorKernel

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

noncomputable def r (eps : ℝ) (w : Vec3) : ℝ :=
  Real.sqrt (‖w‖ ^ 2 + eps ^ 2)

noncomputable def xi (eps : ℝ) (w : Vec3) : Vec3 :=
  (r eps w)⁻¹ • w

/-- Exact algebraic linear map appearing in D xi_eps.
This definition does not claim differentiability; it isolates the operator
that the analytic chain-rule proof must identify. -/
noncomputable def DxiCandidate (eps : ℝ) (w v : Vec3) : Vec3 :=
  (r eps w)⁻¹ • v -
    (((r eps w) ^ 3)⁻¹ * (@inner ℝ Vec3 _ w v)) • w

/-- Equivalent non-unit "I - xi xi^T" form. -/
noncomputable def Pnonunit (eps : ℝ) (w v : Vec3) : Vec3 :=
  v - (@inner ℝ Vec3 _ (xi eps w) v) • xi eps w

theorem r_pos {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    0 < r eps w := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg ‖w‖, sq_pos_of_pos heps]

theorem r_ne_zero {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    r eps w ≠ 0 :=
  ne_of_gt (r_pos heps w)

theorem r_sq {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    (r eps w) ^ 2 = ‖w‖ ^ 2 + eps ^ 2 := by
  unfold r
  rw [Real.sq_sqrt]
  nlinarith [sq_nonneg ‖w‖, sq_pos_of_pos heps]

/-- K1a radial action: the derivative candidate damps the radial component
by eps^2/r^3 rather than annihilating it. -/
theorem DxiCandidate_radial_form
    {eps : ℝ} (heps : 0 < eps) (w : Vec3) :
    DxiCandidate eps w w =
      (eps ^ 2 * ((r eps w) ^ 3)⁻¹) • w := by
  have hr : r eps w ≠ 0 := r_ne_zero heps w
  have hrsq : (r eps w) ^ 2 = ‖w‖ ^ 2 + eps ^ 2 := r_sq heps w
  simp only [DxiCandidate, real_inner_self_eq_norm_sq]
  rw [← sub_smul]
  congr 1
  have hcube : (r eps w) ^ 3 ≠ 0 := pow_ne_zero 3 hr
  have hpoly : (r eps w) ^ 3 - (r eps w) * ‖w‖ ^ 2 =
      (r eps w) * eps ^ 2 := by
    calc
      (r eps w) ^ 3 - (r eps w) * ‖w‖ ^ 2
          = (r eps w) * ((r eps w) ^ 2 - ‖w‖ ^ 2) := by ring
      _ = (r eps w) * eps ^ 2 := by rw [hrsq]; ring
  field_simp [hr, hcube]
  rw [hpoly]
  ring

/-- DxiCandidate is additive in the derivative direction. -/
theorem DxiCandidate_add
    (eps : ℝ) (w a b : Vec3) :
    DxiCandidate eps w (a + b) =
      DxiCandidate eps w a + DxiCandidate eps w b := by
  simp only [DxiCandidate, inner_add_right]
  module

/-- DxiCandidate is homogeneous in the derivative direction. -/
theorem DxiCandidate_smul
    (eps c : ℝ) (w a : Vec3) :
    DxiCandidate eps w (c • a) =
      c • DxiCandidate eps w a := by
  simp only [DxiCandidate, inner_smul_right]
  module

/-- Package the already-proved linear action as a continuous linear map.
Finite dimensionality supplies continuity from linearity. -/
noncomputable def DxiLinearMap (eps : ℝ) (w : Vec3) : Vec3 →ₗ[ℝ] Vec3 where
  toFun := DxiCandidate eps w
  map_add' := DxiCandidate_add eps w
  map_smul' := by
    intro m x
    simpa using DxiCandidate_smul eps m w x

noncomputable def DxiCLM (eps : ℝ) (w : Vec3) : Vec3 →L[ℝ] Vec3 :=
  (DxiLinearMap eps w).toContinuousLinearMap

@[simp] theorem DxiCLM_apply (eps : ℝ) (w v : Vec3) :
    DxiCLM eps w v = DxiCandidate eps w v := rfl

end CriticalBarrier.K1aVectorKernel
