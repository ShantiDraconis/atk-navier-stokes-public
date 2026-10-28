import Mathlib

namespace MPrivate.NS.ThirdCoefficient

structure StrainLinfModel (State : Type*) where
  scale : ℝ → State → State
  strainLinf : State → ℝ → ℝ
  Y : State → ℝ → ℝ
  V : State → ℝ → ℝ

variable {State : Type*}

noncomputable def strainLinfCoefficient
    (C : ℝ) (M : StrainLinfModel State) (u : State) (t : ℝ) : ℝ :=
  C * M.strainLinf u t

/-- T2: `L∞` strain has coefficient weight two. -/
theorem strainLinfCoefficient_scaling
    (C : ℝ) (M : StrainLinfModel State)
    (u : State) (t lambda : ℝ)
    (hscale : M.strainLinf (M.scale lambda u) t =
      lambda ^ 2 * M.strainLinf u (lambda ^ 2 * t)) :
    strainLinfCoefficient C M (M.scale lambda u) t =
      lambda ^ 2 * strainLinfCoefficient C M u (lambda ^ 2 * t) := by
  rw [strainLinfCoefficient, strainLinfCoefficient, hscale]
  ring

/-- T3 repackaging of the classical pointwise estimate.
    The analytic estimate is an explicit hypothesis; T4 is not asserted. -/
theorem strainLinf_T3_of_pointwise_bound
    (C : ℝ) (M : StrainLinfModel State) (u : State) (t : ℝ)
    (h : M.V u t ≤ C * M.strainLinf u t * M.Y u t) :
    M.V u t ≤ strainLinfCoefficient C M u t * M.Y u t := by
  simpa [strainLinfCoefficient, mul_assoc] using h

/-- The missing continuation-level budget is represented only as a goal. -/
def StrainLinfTimeBudgetGoal
    (integratedStrainLinf initialCriticalBudget : ℝ) : Prop :=
  integratedStrainLinf ≤ initialCriticalBudget

end MPrivate.NS.ThirdCoefficient
