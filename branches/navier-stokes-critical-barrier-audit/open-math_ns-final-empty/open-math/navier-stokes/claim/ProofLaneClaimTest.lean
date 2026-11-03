import Mathlib

namespace NSClaimTests.Proof

variable {State : Type}

structure ActualNSData where
  divFree : State → Prop
  energyBound : State → Prop
  regular : State → Prop

structure QuantumClosureOperator where
  closureOp : State → State

structure QuantumClosurePackage
    (D : ActualNSData (State := State)) where
  q : QuantumClosureOperator (State := State)
  preservesDivFree : ∀ u, D.divFree u → D.divFree (q.closureOp u)
  preservesEnergy : ∀ u, D.energyBound u → D.energyBound (q.closureOp u)

def Habitability
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) : Prop :=
  ∀ u, ActualNS u →
    ∃ P : QuantumClosurePackage D,
      D.regular (P.q.closureOp u)

def ProofProducer
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) : Prop :=
  ∀ u, ActualNS u →
    ∃ q : QuantumClosureOperator (State := State),
      (∀ v, D.divFree v → D.divFree (q.closureOp v)) ∧
      (∀ v, D.energyBound v → D.energyBound (q.closureOp v)) ∧
      D.regular (q.closureOp u)

theorem producer_implies_habitability
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (h : ProofProducer D ActualNS) :
    Habitability D ActualNS := by
  intro u hu
  rcases h u hu with ⟨q, hdiv, henergy, hreg⟩
  exact ⟨⟨q, hdiv, henergy⟩, hreg⟩

#print axioms producer_implies_habitability

end NSClaimTests.Proof
