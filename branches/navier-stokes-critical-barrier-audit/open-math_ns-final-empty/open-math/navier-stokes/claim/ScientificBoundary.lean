import Mathlib

namespace NSDualLane.Boundary

inductive LaneStatus where
  | openMath
  | proved
  | refuted
  | failed
  deriving DecidableEq, Repr

structure ScientificBoundary where
  proofLane : LaneStatus
  refutationLane : LaneStatus

def FinalFail (B : ScientificBoundary) : Prop :=
  (B.proofLane = .proved ∧ B.refutationLane = .failed) ∨
  (B.refutationLane = .proved ∧ B.proofLane = .failed)

def Ready (B : ScientificBoundary) : Prop :=
  FinalFail B

theorem ready_requires_asymmetry
    (B : ScientificBoundary)
    (h : Ready B) :
    B.proofLane ≠ B.refutationLane := by
  intro heq
  rcases h with h | h
  · rcases h with ⟨hp, hr⟩
    have hbad : LaneStatus.proved = LaneStatus.failed := by
      calc
        LaneStatus.proved = B.proofLane := hp.symm
        _ = B.refutationLane := heq
        _ = LaneStatus.failed := hr
    cases hbad
  · rcases h with ⟨hr, hp⟩
    have hbad : LaneStatus.proved = LaneStatus.failed := by
      calc
        LaneStatus.proved = B.refutationLane := hr.symm
        _ = B.proofLane := heq.symm
        _ = LaneStatus.failed := hp
    cases hbad

#print axioms ready_requires_asymmetry

end NSDualLane.Boundary
