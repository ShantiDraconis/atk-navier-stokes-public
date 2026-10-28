import Mathlib

namespace MPrivate.NS.ThirdCoefficient

structure VorticityL3Model (State : Type*) where
  scale : ℝ → State → State
  omegaL3 : State → ℝ → ℝ
  Y : State → ℝ → ℝ
  Z : State → ℝ → ℝ
  V : State → ℝ → ℝ

variable {State : Type*}

noncomputable def vorticityL3Coefficient
    (C : ℝ) (M : VorticityL3Model State) (u : State) (t : ℝ) : ℝ :=
  C * (M.omegaL3 u t) ^ 2

/-- Correct T2 scaling for `‖ω‖₃²`. -/
theorem vorticityL3Coefficient_scaling
    (C : ℝ) (M : VorticityL3Model State)
    (u : State) (t lambda : ℝ)
    (hscale : M.omegaL3 (M.scale lambda u) t = lambda * M.omegaL3 u (lambda ^ 2 * t)) :
    vorticityL3Coefficient C M (M.scale lambda u) t =
      lambda ^ 2 * vorticityL3Coefficient C M u (lambda ^ 2 * t) := by
  rw [vorticityL3Coefficient, vorticityL3Coefficient, hscale]
  ring

/-- The analytic stretching estimate for this candidate is deliberately not asserted.
    When supplied externally, the algebraic repackaging is exact. -/
theorem vorticityL3_T3_of_analytic_estimate
    (ε C : ℝ) (M : VorticityL3Model State) (u : State) (t : ℝ)
    (h : M.V u t ≤ ε * M.Z u t +
      C * (M.omegaL3 u t) ^ 2 * M.Y u t) :
    M.V u t ≤ ε * M.Z u t +
      vorticityL3Coefficient C M u t * M.Y u t := by
  simpa [vorticityL3Coefficient, mul_assoc] using h

end MPrivate.NS.ThirdCoefficient
