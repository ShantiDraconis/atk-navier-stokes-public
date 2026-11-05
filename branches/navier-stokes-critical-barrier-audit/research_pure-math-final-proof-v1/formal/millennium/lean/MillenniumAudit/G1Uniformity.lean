import MillenniumAudit.G1Audit

namespace MillenniumAudit.G1Uniformity

open MillenniumAudit.G1Audit

def PointwiseClosedDepletion
    {State : Type}
    (ActualNS : State → Prop)
    (stretching dissipation : State → ℝ) : Prop :=
  ∀ u : State, ActualNS u →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      stretching u ≤ (1 - δ) * dissipation u

theorem uniform_implies_pointwise
    {State : Type}
    {ActualNS : State → Prop}
    {stretching dissipation : State → ℝ}
    (h : G1ClosedForActualNS ActualNS stretching dissipation) :
    PointwiseClosedDepletion ActualNS stretching dissipation := by
  rcases h with ⟨δ, hδ, hδ1, hall⟩
  intro u hu
  exact ⟨δ, hδ, hδ1, hall u hu⟩

/-- The precise missing quantifier bridge. It is data, not an axiom. -/
structure UniformizationBridge
    {State : Type}
    (ActualNS : State → Prop)
    (stretching dissipation : State → ℝ) : Prop where
  promote :
    PointwiseClosedDepletion ActualNS stretching dissipation →
      G1ClosedForActualNS ActualNS stretching dissipation

theorem bridge_closes_uniform_G1
    {State : Type}
    {ActualNS : State → Prop}
    {stretching dissipation : State → ℝ}
    (B : UniformizationBridge ActualNS stretching dissipation)
    (hPointwise : PointwiseClosedDepletion ActualNS stretching dissipation) :
    G1ClosedForActualNS ActualNS stretching dissipation :=
  B.promote hPointwise

/-- A concrete sufficient condition for uniformization: a single positive lower
    bound for all statewise depletion witnesses.  The missing PDE content is therefore
    isolated in proving such a lower bound for the ActualNS class. -/
def UniformGapLowerBound
    {State : Type}
    (ActualNS : State → Prop)
    (stretching dissipation : State → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ u : State, ActualNS u →
      stretching u ≤ (1 - δ) * dissipation u

theorem uniformGapLowerBound_closes_G1
    {State : Type}
    {ActualNS : State → Prop}
    {stretching dissipation : State → ℝ}
    (h : UniformGapLowerBound ActualNS stretching dissipation) :
    G1ClosedForActualNS ActualNS stretching dissipation := by
  exact h

/-- Toy family exposing the quantifier obstruction:
    each state has a positive depletion gap, but no single positive gap works
    uniformly over all states. -/
def toyActualNS (u : ℝ) : Prop := 0 < u ∧ u ≤ 1

def toyStretching (u : ℝ) : ℝ := 1 - u

def toyDissipation (_u : ℝ) : ℝ := 1

theorem toy_pointwise :
    PointwiseClosedDepletion toyActualNS toyStretching toyDissipation := by
  intro u hu
  rcases hu with ⟨hu0, hu1⟩
  refine ⟨u, hu0, hu1, ?_⟩
  simp [toyStretching, toyDissipation]

theorem toy_not_uniform :
    ¬ G1ClosedForActualNS toyActualNS toyStretching toyDissipation := by
  intro h
  rcases h with ⟨δ, hδ, hδ1, hall⟩
  have hu0 : 0 < δ / 2 := by linarith
  have hu1 : δ / 2 ≤ 1 := by linarith
  have htoy : toyActualNS (δ / 2) := ⟨hu0, hu1⟩
  have hineq := hall (δ / 2) htoy
  dsimp [toyStretching, toyDissipation] at hineq
  linarith

theorem pointwise_does_not_imply_uniform_in_general :
    ¬ (∀ {State : Type}
        (ActualNS : State → Prop)
        (stretching dissipation : State → ℝ),
        PointwiseClosedDepletion ActualNS stretching dissipation →
          G1ClosedForActualNS ActualNS stretching dissipation) := by
  intro h
  exact toy_not_uniform
    (h toyActualNS toyStretching toyDissipation toy_pointwise)

#print axioms uniform_implies_pointwise
#print axioms bridge_closes_uniform_G1
#print axioms toy_pointwise
#print axioms toy_not_uniform
#print axioms pointwise_does_not_imply_uniform_in_general

end MillenniumAudit.G1Uniformity
