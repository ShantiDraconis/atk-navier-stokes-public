import Mathlib

namespace NSDeltaUniformityAudit

def UniformDelta
    {State : Type}
    (ActualNS : State → Prop)
    (stretching dissipation : State → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ u : State, ActualNS u →
      stretching u ≤ (1 - δ) * dissipation u

def PointwiseDelta
    {State : Type}
    (ActualNS : State → Prop)
    (stretching dissipation : State → ℝ) : Prop :=
  ∀ u : State, ActualNS u →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      stretching u ≤ (1 - δ) * dissipation u

theorem uniform_delta_implies_pointwise
    {State : Type}
    {ActualNS : State → Prop}
    {stretching dissipation : State → ℝ}
    (h : UniformDelta ActualNS stretching dissipation) :
    PointwiseDelta ActualNS stretching dissipation := by
  rcases h with ⟨δ, hδ, hδ1, hAll⟩
  intro u hu
  exact ⟨δ, hδ, hδ1, hAll u hu⟩

def DeltaQuantifierResidue
    {State : Type}
    (ActualNS : State → Prop)
    (stretching dissipation : State → ℝ) : Prop :=
  PointwiseDelta ActualNS stretching dissipation ∧
  ¬ UniformDelta ActualNS stretching dissipation

#print axioms NSDeltaUniformityAudit.uniform_delta_implies_pointwise

end NSDeltaUniformityAudit
