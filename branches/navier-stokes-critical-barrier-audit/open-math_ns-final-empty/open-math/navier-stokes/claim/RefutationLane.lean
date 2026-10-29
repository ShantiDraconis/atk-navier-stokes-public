import Mathlib

namespace NSDualLane.Refutation

variable {State : Type}

structure ActualNSData where
  energyBound : State → Prop
  regular : State → Prop

structure CandidateWitness where
  act : State → State

structure CriticalBalance where
  carrier : State
  balanced : Prop

structure MinimalCut where
  balance : CriticalBalance (State := State)
  crossed : Prop

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

structure RefutationLane
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) where
  toBalance : ∀ u, ActualNS u → CriticalBalance (State := State)
  toCut : ∀ u, ActualNS u → MinimalCut (State := State)
  exclusion : ProvedExclusion D ActualNS

def RefutedFormulation
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop) : Prop :=
  ProvedExclusion D ActualNS

theorem refutation_lane_implies_refuted
    (D : ActualNSData (State := State))
    (ActualNS : State → Prop)
    (L : RefutationLane D ActualNS) :
    RefutedFormulation D ActualNS :=
  L.exclusion

#print axioms refutation_lane_implies_refuted

end NSDualLane.Refutation
