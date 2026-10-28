import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-- Abstract scalar interface for the candidate `a₃ = C ‖S‖₃²`.
    This file proves only algebraic consequences of explicitly supplied analytic estimates. -/
structure StrainL3Model (State : Type*) where
  scale : ℝ → State → State
  strainL3 : State → ℝ → ℝ
  Y : State → ℝ → ℝ
  Z : State → ℝ → ℝ
  V : State → ℝ → ℝ

variable {State : Type*}

noncomputable def strainL3Coefficient
    (C : ℝ) (M : StrainL3Model State) (u : State) (t : ℝ) : ℝ :=
  C * (M.strainL3 u t) ^ 2

/-- T2 for the candidate follows from the correct weight-one scaling of `‖S‖₃`. -/
theorem strainL3Coefficient_scaling
    (C : ℝ) (M : StrainL3Model State)
    (u : State) (t lambda : ℝ)
    (hscale : M.strainL3 (M.scale lambda u) t = lambda * M.strainL3 u (lambda ^ 2 * t)) :
    strainL3Coefficient C M (M.scale lambda u) t =
      lambda ^ 2 * strainL3Coefficient C M u (lambda ^ 2 * t) := by
  rw [strainL3Coefficient, strainL3Coefficient, hscale]
  ring

/-- T3 is recorded honestly: once the analytic Hölder+GN+Young estimate has been
    established for the concrete NS model, it has exactly the required evolution form. -/
theorem strainL3_T3_of_analytic_estimate
    (ε C : ℝ) (M : StrainL3Model State) (u : State) (t : ℝ)
    (h : M.V u t ≤ ε * M.Z u t +
      C * (M.strainL3 u t) ^ 2 * M.Y u t) :
    M.V u t ≤ ε * M.Z u t +
      strainL3Coefficient C M u t * M.Y u t := by
  simpa [strainL3Coefficient, mul_assoc] using h

/-- Nonnegativity of the coefficient when `C ≥ 0`. -/
theorem strainL3Coefficient_nonneg
    {C : ℝ} (hC : 0 ≤ C) (M : StrainL3Model State) (u : State) (t : ℝ) :
    0 ≤ strainL3Coefficient C M u t := by
  exact mul_nonneg hC (sq_nonneg _)

end MPrivate.NS.ThirdCoefficient
