import Mathlib

/-!
K1a algebraic kernel: exact regularised-direction identities.

This file deliberately proves only finite-dimensional scalar/algebraic facts.
No PDE regularity estimate, remainder convergence, or cutoff-free bound is
claimed here.
-/

namespace CriticalBarrier.K1aXiEps

/-- Regularised radius in scalar squared-norm coordinates. -/
noncomputable def rSq (eps q : ℝ) : ℝ := q + eps ^ 2

/-- For positive epsilon and nonnegative squared norm, the radicand is positive. -/
theorem rSq_pos {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    0 < rSq eps q := by
  dsimp [rSq]
  nlinarith [sq_pos_of_pos heps]

/-- Hence the regularised radius is strictly positive. -/
theorem sqrt_rSq_pos {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    0 < Real.sqrt (rSq eps q) := by
  exact Real.sqrt_pos.2 (rSq_pos heps hq)

/-- The regularised radius is at least epsilon. -/
theorem eps_le_sqrt_rSq {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    eps ≤ Real.sqrt (rSq eps q) := by
  rw [← Real.sqrt_sq_eq_abs eps]
  rw [abs_of_pos heps]
  apply Real.sqrt_le_sqrt
  dsimp [rSq]
  nlinarith

/-- Scalar identity behind the non-unit radial defect:
    1 - q/(q+eps^2) = eps^2/(q+eps^2). -/
theorem radial_defect_scalar {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    1 - q / rSq eps q = eps ^ 2 / rSq eps q := by
  have hne : rSq eps q ≠ 0 := ne_of_gt (rSq_pos heps hq)
  field_simp [hne]
  ring

/-- Radial eigenvalue identity:
    1/r - q/r^3 = eps^2/r^3 when r^2=q+eps^2. -/
theorem radial_eigenvalue_scalar
    {eps q r : ℝ}
    (hr : r ^ 2 = rSq eps q)
    (hr0 : r ≠ 0) :
    1 / r - q / r ^ 3 = eps ^ 2 / r ^ 3 := by
  have hq : q = r ^ 2 - eps ^ 2 := by
    dsimp [rSq] at hr
    nlinarith
  rw [hq]
  field_simp [hr0]
  ring

/-- The purely algebraic coefficient eps^2/r^2 is bounded by one whenever
    r^2=q+eps^2 and q is nonnegative. -/
theorem eps_sq_div_rsq_le_one
    {eps q r : ℝ}
    (hq : 0 ≤ q)
    (hr : r ^ 2 = rSq eps q)
    (hr0 : r ≠ 0) :
    eps ^ 2 / r ^ 2 ≤ 1 := by
  have hrsq : 0 < r ^ 2 := sq_pos_of_ne_zero hr0
  have he : eps ^ 2 ≤ r ^ 2 := by
    dsimp [rSq] at hr
    nlinarith
  exact (div_le_one hrsq).2 he

end CriticalBarrier.K1aXiEps
