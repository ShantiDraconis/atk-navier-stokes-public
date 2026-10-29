/-
XiEpsExactAlgebra.lean
Kernel-checkable algebra for the regularised direction.
No PDE regularity claim is made here.
-/
import Mathlib

noncomputable section

namespace G1XiEpsExactAlgebra

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

noncomputable def r_eps (eps : ℝ) (omega : Vec3) : ℝ :=
  Real.sqrt (‖omega‖ ^ 2 + eps ^ 2)

noncomputable def xi_eps (eps : ℝ) (omega : Vec3) : Vec3 :=
  (r_eps eps omega)⁻¹ • omega

/-- Exact algebraic linearisation candidate:
    r⁻¹ v - r⁻³ <omega,v> omega.
    The HasFDerivAt identification is deliberately kept separate from this
    definition so no analytic claim is hidden in an interface field. -/
noncomputable def xiEpsLinearized (eps : ℝ) (omega v : Vec3) : Vec3 :=
  (r_eps eps omega)⁻¹ • v -
    ((r_eps eps omega)⁻¹ ^ 3 * @inner ℝ Vec3 _ omega v) • omega

lemma r_eps_sq (eps : ℝ) (omega : Vec3) :
    (r_eps eps omega) ^ 2 = ‖omega‖ ^ 2 + eps ^ 2 := by
  unfold r_eps
  rw [sq_sqrt]
  positivity

lemma r_eps_pos {eps : ℝ} (heps : 0 < eps) (omega : Vec3) :
    0 < r_eps eps omega := by
  unfold r_eps
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg ‖omega‖]

lemma r_eps_ne_zero {eps : ℝ} (heps : 0 < eps) (omega : Vec3) :
    r_eps eps omega ≠ 0 :=
  ne_of_gt (r_eps_pos heps omega)

lemma eps_sq_le_r_eps_sq (eps : ℝ) (omega : Vec3) :
    eps ^ 2 ≤ (r_eps eps omega) ^ 2 := by
  rw [r_eps_sq]
  positivity

lemma xi_eps_eq_inv_smul (eps : ℝ) (omega : Vec3) :
    xi_eps eps omega = (r_eps eps omega)⁻¹ • omega := rfl

/-- The exact operator is not silently identified with an orthogonal
    projection.  This definition records the radial correction explicitly. -/
noncomputable def radialCoefficient (eps : ℝ) (omega : Vec3) : ℝ :=
  eps ^ 2 * (r_eps eps omega)⁻¹ ^ 3

lemma radialCoefficient_nonneg (eps : ℝ) (omega : Vec3) :
    0 ≤ radialCoefficient eps omega := by
  unfold radialCoefficient
  positivity

lemma radialCoefficient_pos {eps : ℝ} (heps : 0 < eps) (omega : Vec3) :
    0 < radialCoefficient eps omega := by
  unfold radialCoefficient
  have hr : 0 < r_eps eps omega := r_eps_pos heps omega
  positivity

/-- Fail-closed boundary: PDE evolution, L1 remainder convergence and
    cutoff-free estimates are not consequences of the algebra above. -/
structure PDELiftObligations where
  exact_material_chain_rule : Prop
  remainder_vanishes_L1 : Prop
  cutoff_free_remainder_bound : Prop

end G1XiEpsExactAlgebra
