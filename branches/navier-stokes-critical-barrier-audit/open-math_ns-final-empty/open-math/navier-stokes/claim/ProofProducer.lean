import Mathlib

namespace NSClaimProducers.ProofLane

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

structure ProofInputs
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) where
  closureOp : State → State
  div_free_preserved :
    ∀ v, D.divFree v → D.divFree (closureOp v)
  energy_bound_preserved :
    ∀ v, D.energyBound v → D.energyBound (closureOp v)
  closure_preserves_actual_state :
    ∀ u, ActualNS u → closureOp u = u
  regular_after_closure :
    ∀ u, ActualNS u → D.regular (closureOp u)

def toPackage
    (D : ActualNSData (State := State))
    (I : ProofInputs D ActualNS) :
    QuantumClosurePackage D where
  q := ⟨I.closureOp⟩
  preservesDivFree := I.div_free_preserved
  preservesEnergy := I.energy_bound_preserved

/-- Adapter for certified downstream regularity theorems.
    Once a genuine theorem `forall u, ActualNS u -> regular u` exists, the
    proof producer is inhabited by the identity closure.  No new PDE content
    is introduced here. -/
def of_actual_regularity
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (hreg : ∀ u, ActualNS u → D.regular u) :
    ProofInputs D ActualNS where
  closureOp := id
  div_free_preserved := by
    intro v hv
    simpa using hv
  energy_bound_preserved := by
    intro v hv
    simpa using hv
  closure_preserves_actual_state := by
    intro u hu
    rfl
  regular_after_closure := by
    intro u hu
    simpa using hreg u hu

theorem inputs_imply_habitability
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (I : ProofInputs D ActualNS) :
    Habitability D ActualNS := by
  intro u hu
  refine ⟨toPackage D I, ?_⟩
  exact I.regular_after_closure u hu


theorem actual_regularity_implies_habitability
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (hreg : ∀ u, ActualNS u → D.regular u) :
    Habitability D ActualNS := by
  exact inputs_imply_habitability D ActualNS
    (of_actual_regularity D ActualNS hreg)

theorem inputs_imply_actual_regularity
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (I : ProofInputs D ActualNS) :
    ∀ u, ActualNS u → D.regular u := by
  intro u hu
  have hreg := I.regular_after_closure u hu
  rw [I.closure_preserves_actual_state u hu] at hreg
  exact hreg

#print axioms of_actual_regularity
#print axioms inputs_imply_habitability
#print axioms actual_regularity_implies_habitability
#print axioms inputs_imply_actual_regularity

end NSClaimProducers.ProofLane
