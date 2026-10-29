import Mathlib

namespace NSHabitantCertificate

universe u v

variable {InitialData : Type u} {VelocityField : Type v}

structure NSGlobalHabitant
    (SolvesNavierStokes : InitialData → (ℝ → VelocityField) → Prop)
    (SmoothGlobal : (ℝ → VelocityField) → Prop) where
  solve : InitialData → ℝ → VelocityField
  isSolution : ∀ u0, SolvesNavierStokes u0 (solve u0)
  smoothGlobal : ∀ u0, SmoothGlobal (solve u0)

structure NSBlowUpHabitant
    (FiniteTimeBlowUp : InitialData → ℝ → Prop) where
  u0star : InitialData
  Tstar : ℝ
  Tstar_pos : 0 < Tstar
  blowsUp : FiniteTimeBlowUp u0star Tstar

abbrev NSHabitant
    (SolvesNavierStokes : InitialData → (ℝ → VelocityField) → Prop)
    (SmoothGlobal : (ℝ → VelocityField) → Prop)
    (FiniteTimeBlowUp : InitialData → ℝ → Prop) :=
  NSGlobalHabitant SolvesNavierStokes SmoothGlobal ⊕
  NSBlowUpHabitant FiniteTimeBlowUp

def GlobalRegularityClaim
    (SolvesNavierStokes : InitialData → (ℝ → VelocityField) → Prop)
    (SmoothGlobal : (ℝ → VelocityField) → Prop) : Prop :=
  ∀ u0 : InitialData, ∃ u : ℝ → VelocityField,
    SolvesNavierStokes u0 u ∧ SmoothGlobal u

def BlowUpClaim
    (FiniteTimeBlowUp : InitialData → ℝ → Prop) : Prop :=
  ∃ u0 : InitialData, ∃ T : ℝ,
    0 < T ∧ FiniteTimeBlowUp u0 T

theorem ns_closed_of_global
    (SolvesNavierStokes : InitialData → (ℝ → VelocityField) → Prop)
    (SmoothGlobal : (ℝ → VelocityField) → Prop)
    (H : NSGlobalHabitant SolvesNavierStokes SmoothGlobal) :
    GlobalRegularityClaim SolvesNavierStokes SmoothGlobal := by
  intro u0
  exact ⟨H.solve u0, H.isSolution u0, H.smoothGlobal u0⟩

theorem ns_closed_of_blowup
    (FiniteTimeBlowUp : InitialData → ℝ → Prop)
    (H : NSBlowUpHabitant FiniteTimeBlowUp) :
    BlowUpClaim FiniteTimeBlowUp := by
  exact ⟨H.u0star, H.Tstar, H.Tstar_pos, H.blowsUp⟩

theorem inhabitant_closes_terminal
    (SolvesNavierStokes : InitialData → (ℝ → VelocityField) → Prop)
    (SmoothGlobal : (ℝ → VelocityField) → Prop)
    (FiniteTimeBlowUp : InitialData → ℝ → Prop)
    (H : NSHabitant SolvesNavierStokes SmoothGlobal FiniteTimeBlowUp) :
    GlobalRegularityClaim SolvesNavierStokes SmoothGlobal ∨
    BlowUpClaim FiniteTimeBlowUp := by
  cases H with
  | inl h =>
      exact Or.inl (ns_closed_of_global SolvesNavierStokes SmoothGlobal h)
  | inr h =>
      exact Or.inr (ns_closed_of_blowup FiniteTimeBlowUp h)

def OpenMathProducer
    (SolvesNavierStokes : InitialData → (ℝ → VelocityField) → Prop)
    (SmoothGlobal : (ℝ → VelocityField) → Prop)
    (FiniteTimeBlowUp : InitialData → ℝ → Prop) : Prop :=
  Nonempty (NSHabitant SolvesNavierStokes SmoothGlobal FiniteTimeBlowUp)

theorem open_math_producer_closes_terminal
    (SolvesNavierStokes : InitialData → (ℝ → VelocityField) → Prop)
    (SmoothGlobal : (ℝ → VelocityField) → Prop)
    (FiniteTimeBlowUp : InitialData → ℝ → Prop)
    (h : OpenMathProducer SolvesNavierStokes SmoothGlobal FiniteTimeBlowUp) :
    GlobalRegularityClaim SolvesNavierStokes SmoothGlobal ∨
    BlowUpClaim FiniteTimeBlowUp := by
  rcases h with ⟨H⟩
  exact inhabitant_closes_terminal
    SolvesNavierStokes SmoothGlobal FiniteTimeBlowUp H

#print axioms ns_closed_of_global
#print axioms ns_closed_of_blowup
#print axioms inhabitant_closes_terminal
#print axioms open_math_producer_closes_terminal

end NSHabitantCertificate
