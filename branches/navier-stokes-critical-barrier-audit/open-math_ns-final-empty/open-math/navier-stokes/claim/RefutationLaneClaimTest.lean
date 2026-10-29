import Mathlib

namespace NSClaimTests.Refutation

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

def RefutationProducer
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) : Prop :=
  ∀ w : CandidateWitness (State := State),
    ∃ u, ActualNS u ∧
      (¬ D.regular (w.act u) ∨
       (D.energyBound u ∧ ¬ D.energyBound (w.act u)))

theorem producer_implies_exclusion
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (h : RefutationProducer D ActualNS) :
    ProvedExclusion D ActualNS := by
  intro w
  exact h w

#print axioms producer_implies_exclusion

end NSClaimTests.Refutation
