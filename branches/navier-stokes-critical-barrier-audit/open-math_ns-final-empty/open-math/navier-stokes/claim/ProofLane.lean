import Mathlib

namespace NSDualLane.Proof

variable {State Q : Type}

structure ActualNSData where
  divFree : State → Prop
  energyBound : State → Prop
  regular : State → Prop

structure QuantumClosureOperator where
  closureOp : State → State

def PreservesDivFree
    (D : ActualNSData (State := State))
    (q : QuantumClosureOperator (State := State)) : Prop :=
  ∀ u, D.divFree u → D.divFree (q.closureOp u)

def PreservesEnergy
    (D : ActualNSData (State := State))
    (q : QuantumClosureOperator (State := State)) : Prop :=
  ∀ u, D.energyBound u → D.energyBound (q.closureOp u)

structure CriticalBalance where
  carrier : State
  balanced : Prop

structure MinimalCut where
  balance : CriticalBalance (State := State)
  crossed : Prop

structure QuantumClosurePackage
    (D : ActualNSData (State := State)) where
  q : QuantumClosureOperator (State := State)
  preservesDivFree : PreservesDivFree D q
  preservesEnergy : PreservesEnergy D q

def Habitability
    (D : ActualNSData (State := State))
    (u : State) : Prop :=
  ∃ P : QuantumClosurePackage D,
    D.regular (P.q.closureOp u)

structure ProofLane
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) where
  toBalance : ∀ u, ActualNS u → CriticalBalance (State := State)
  toCut : ∀ u, ActualNS u → MinimalCut (State := State)
  package : ∀ u, ActualNS u → QuantumClosurePackage D
  regularized : ∀ u (hu : ActualNS u),
    D.regular ((package u hu).q.closureOp u)

theorem proof_lane_implies_habitability
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (L : ProofLane D ActualNS) :
    ∀ u, ActualNS u → Habitability D u := by
  intro u hu
  exact ⟨L.package u hu, L.regularized u hu⟩

#print axioms proof_lane_implies_habitability

end NSDualLane.Proof
