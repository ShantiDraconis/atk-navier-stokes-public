import Mathlib

namespace CriticalBarrier.K1aXiEps

noncomputable def rSq (eps q : ℝ) : ℝ := q + eps ^ 2

theorem rSq_pos {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    0 < rSq eps q := by
  dsimp [rSq]
  nlinarith [sq_pos_of_pos heps]

theorem sqrt_rSq_pos {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    0 < Real.sqrt (rSq eps q) := by
  exact Real.sqrt_pos.2 (rSq_pos heps hq)

theorem radial_defect_scalar {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    1 - q / rSq eps q = eps ^ 2 / rSq eps q := by
  have hne : rSq eps q ≠ 0 := ne_of_gt (rSq_pos heps hq)
  field_simp [hne]
  simp [rSq]

theorem radial_eigenvalue_scalar
    {eps q r : ℝ} (hr : r ^ 2 = rSq eps q) (hr0 : r ≠ 0) :
    1 / r - q / r ^ 3 = eps ^ 2 / r ^ 3 := by
  have hqeq : q = r ^ 2 - eps ^ 2 := by
    dsimp [rSq] at hr
    nlinarith
  rw [hqeq]
  field_simp [hr0]
  ring

theorem eps_sq_div_rsq_le_one
    {eps q r : ℝ} (hq : 0 ≤ q)
    (hr : r ^ 2 = rSq eps q) (hr0 : r ≠ 0) :
    eps ^ 2 / r ^ 2 ≤ 1 := by
  have hrsq : 0 < r ^ 2 := sq_pos_of_ne_zero hr0
  have he : eps ^ 2 ≤ r ^ 2 := by
    dsimp [rSq] at hr
    nlinarith
  exact (div_le_one hrsq).2 he

end CriticalBarrier.K1aXiEps
