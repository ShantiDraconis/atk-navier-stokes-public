import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# SixBlockScaling

Scaling model for an integrated vortex-stretching interaction. Pointwise strain
and vorticity each have NS degree +2, while the spatial Jacobian contributes
-3. Hence every integrated block has degree +3.
-/

/-- Scalar model of one integrated trilinear block including the volume factor. -/
def integratedBlock (jac strain omega1 omega2 : ℝ) : ℝ :=
  jac * strain * omega1 * omega2

/-- Under NS scaling `strain,omega -> lambda^2`, `jac -> lambda^-3`, every block
has net degree +3. The inverse Jacobian is encoded as division by `lambda^3`. -/
theorem integratedBlock_scales_degree_three
    (jac strain omega1 omega2 lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    integratedBlock
      (jac / lambda^3)
      (lambda^2 * strain)
      (lambda^2 * omega1)
      (lambda^2 * omega2) =
    lambda^3 * integratedBlock jac strain omega1 omega2 := by
  unfold integratedBlock
  field_simp [hlambda]

/-- Abstract degree-three predicate for an integrated interaction. -/
def IntegratedDegreeThree (V Vscaled lambda : ℝ) : Prop :=
  Vscaled = lambda^3 * V

/-- If six signed blocks each scale with degree three, their signed sum does too. -/
theorem six_degree_three_blocks_sum_degree_three
    (v1 v2 v3 v4 v5 v6
      w1 w2 w3 w4 w5 w6 lambda : ℝ)
    (h1 : IntegratedDegreeThree v1 w1 lambda)
    (h2 : IntegratedDegreeThree v2 w2 lambda)
    (h3 : IntegratedDegreeThree v3 w3 lambda)
    (h4 : IntegratedDegreeThree v4 w4 lambda)
    (h5 : IntegratedDegreeThree v5 w5 lambda)
    (h6 : IntegratedDegreeThree v6 w6 lambda) :
    IntegratedDegreeThree
      (v1 + v2 + v3 + v4 + v5 + v6)
      (w1 + w2 + w3 + w4 + w5 + w6)
      lambda := by
  unfold IntegratedDegreeThree at *
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- A degree-two coefficient multiplying degree-one enstrophy matches the
required degree-three block homogeneity. -/
theorem coefficient_times_enstrophy_matches_block_scaling
    (a aScaled Y YScaled lambda : ℝ)
    (ha : aScaled = lambda^2 * a)
    (hY : YScaled = lambda * Y) :
    aScaled * YScaled = lambda^3 * (a * Y) := by
  rw [ha, hY]
  ring

end MPrivate.NS.ThirdCoefficient
