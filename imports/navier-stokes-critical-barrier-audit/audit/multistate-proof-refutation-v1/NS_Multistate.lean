import Mathlib

namespace NSMultistateAudit

inductive ClosureStatus
  | hypotheticalClosed
  | proved
  | residue
  deriving Repr, DecidableEq

structure HypotheticalClosedChain
    (C_START C_CENTER C_END : Prop) where
  start_to_center : C_START → C_CENTER
  center_to_end : C_CENTER → C_END

structure RegularityWitness
    {State : Type}
    (ActualNS GlobalRegularity : State → Prop) where
  closes : ∀ u, ActualNS u → GlobalRegularity u

structure BreakdownWitness
    {State : Type}
    (ActualNS Breakdown : State → Prop) where
  state : State
  actual : ActualNS state
  breaks : Breakdown state

inductive BilateralWitness
    {State : Type}
    (ActualNS GlobalRegularity Breakdown : State → Prop) where
  | regularity :
      RegularityWitness ActualNS GlobalRegularity →
      BilateralWitness ActualNS GlobalRegularity Breakdown
  | breakdown :
      BreakdownWitness ActualNS Breakdown →
      BilateralWitness ActualNS GlobalRegularity Breakdown

def C_END
    {State : Type}
    (ActualNS GlobalRegularity Breakdown : State → Prop) : Prop :=
  (∀ u, ActualNS u → GlobalRegularity u) ∨
  (∃ u, ActualNS u ∧ Breakdown u)

theorem bilateral_witness_to_end
    {State : Type}
    {ActualNS GlobalRegularity Breakdown : State → Prop}
    (h : BilateralWitness ActualNS GlobalRegularity Breakdown) :
    C_END ActualNS GlobalRegularity Breakdown := by
  cases h with
  | regularity hR =>
      exact Or.inl hR.closes
  | breakdown hB =>
      exact Or.inr ⟨hB.state, hB.actual, hB.breaks⟩

theorem hypothetical_chain_composes
    {C_START C_CENTER C_END : Prop}
    (H : HypotheticalClosedChain C_START C_CENTER C_END)
    (hStart : C_START) :
    C_END :=
  H.center_to_end (H.start_to_center hStart)

#print axioms NSMultistateAudit.bilateral_witness_to_end
#print axioms NSMultistateAudit.hypothetical_chain_composes

end NSMultistateAudit
