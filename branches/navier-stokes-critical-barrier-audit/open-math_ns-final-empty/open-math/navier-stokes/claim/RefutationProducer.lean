import Mathlib

namespace NSClaimProducers.RefutationLane

variable {State : Type}

structure ActualNSData where
  energyBound : State → Prop
  regular : State → Prop

structure CandidateWitness where
  act : State → State

def BreaksEnergy
    (D : ActualNSData (State := State))
    (w : CandidateWitness (State := State))
    (u : State) : Prop :=
  D.energyBound u ∧ ¬ D.energyBound (w.act u)

def BlowupOrFailure
    (D : ActualNSData (State := State))
    (w : CandidateWitness (State := State))
    (u : State) : Prop :=
  ¬ D.regular (w.act u) ∨ BreaksEnergy D w u

def ProvedExclusion
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) : Prop :=
  ∀ w : CandidateWitness (State := State),
    ∃ u, ActualNS u ∧ BlowupOrFailure D w u

structure RefutationInputs
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) where
  witness_break :
    ∀ w : CandidateWitness (State := State),
      ∃ u, ActualNS u ∧
        (¬ D.regular (w.act u) ∨
         (D.energyBound u ∧ ¬ D.energyBound (w.act u)))

def toProducer
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (I : RefutationInputs D ActualNS) :
    ProvedExclusion D ActualNS := by
  intro w
  rcases I.witness_break w with ⟨u, hu, hbreak⟩
  exact ⟨u, hu, hbreak⟩

theorem inputs_imply_exclusion
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (I : RefutationInputs D ActualNS) :
    ProvedExclusion D ActualNS :=
  toProducer D ActualNS I


/-- Identity witness exposes the true scientific strength of ProvedExclusion:
    any universal exclusion certificate must contain an actual NS state whose
    regularity predicate fails.  The energy-break branch is contradictory for
    the identity map. -/
def identityWitness : CandidateWitness (State := State) where
  act := id

theorem exclusion_implies_actual_irregular
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (h : ProvedExclusion D ActualNS) :
    ∃ u, ActualNS u ∧ ¬ D.regular u := by
  rcases h (identityWitness (State := State)) with ⟨u, hu, hbreak⟩
  refine ⟨u, hu, ?_⟩
  rcases hbreak with hirreg | henergy
  · simpa [identityWitness] using hirreg
  · rcases henergy with ⟨hE, hnE⟩
    exfalso
    exact hnE (by simpa [identityWitness] using hE)

theorem all_actual_regular_excludes_refutation
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (hreg : ∀ u, ActualNS u → D.regular u) :
    ¬ ProvedExclusion D ActualNS := by
  intro h
  rcases exclusion_implies_actual_irregular D ActualNS h with ⟨u, hu, hirreg⟩
  exact hirreg (hreg u hu)

#print axioms exclusion_implies_actual_irregular
#print axioms all_actual_regular_excludes_refutation
#print axioms toProducer
#print axioms inputs_imply_exclusion

end NSClaimProducers.RefutationLane
