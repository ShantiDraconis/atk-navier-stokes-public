import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# DecomposedA3Certificates

Pure certificates for T1/T2 of a decomposed ThirdCoefficient.
No PDE estimate and no time-integral budget is asserted here.
-/

variable {State : Type*}

/-- Sum of the three candidate mechanisms. -/
def a3Sum
    (aLow aCross aAlign : State → ℝ → ℝ)
    (u : State) (t : ℝ) : ℝ :=
  aLow u t + aCross u t + aAlign u t

/-- Componentwise nonnegativity gives T1 for the sum. -/
theorem a3Sum_nonnegative
    (aLow aCross aAlign : State → ℝ → ℝ)
    (hLow : ∀ u t, 0 ≤ aLow u t)
    (hCross : ∀ u t, 0 ≤ aCross u t)
    (hAlign : ∀ u t, 0 ≤ aAlign u t) :
    ∀ u t, 0 ≤ a3Sum aLow aCross aAlign u t := by
  intro u t
  unfold a3Sum
  exact add_nonneg (add_nonneg (hLow u t) (hCross u t)) (hAlign u t)

/-- Critical scaling law for one component. -/
def ComponentCriticalScaling
    (scale : ℝ → State → State)
    (a : State → ℝ → ℝ) : Prop :=
  ∀ u t lambda, 0 < lambda →
    a (scale lambda u) t = lambda^2 * a u (lambda^2 * t)

/-- Componentwise degree-2 scaling gives T2 for the sum. -/
theorem a3Sum_critical_scaling
    (scale : ℝ → State → State)
    (aLow aCross aAlign : State → ℝ → ℝ)
    (hLow : ComponentCriticalScaling scale aLow)
    (hCross : ComponentCriticalScaling scale aCross)
    (hAlign : ComponentCriticalScaling scale aAlign) :
    ComponentCriticalScaling scale (a3Sum aLow aCross aAlign) := by
  intro u t lambda hlambda
  unfold a3Sum
  rw [hLow u t lambda hlambda, hCross u t lambda hlambda, hAlign u t lambda hlambda]
  ring

/-- T1/T2 are therefore infrastructure gates.  The mathematical frontier starts
at T3 (signed PDE domination) and T4c (independent L1 budget). -/
structure DecomposedA3Infrastructure where
  low_nonnegative : Prop
  cross_nonnegative : Prop
  align_nonnegative : Prop
  low_critical_scaling : Prop
  cross_critical_scaling : Prop
  align_critical_scaling : Prop

end MPrivate.NS.ThirdCoefficient
