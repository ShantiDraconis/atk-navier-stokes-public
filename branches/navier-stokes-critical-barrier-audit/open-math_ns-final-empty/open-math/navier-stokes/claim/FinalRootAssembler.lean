import Mathlib

namespace NSFinalAssembler

inductive LaneOutcome where
  | openMath
  | proved
  | refuted
  | failed
  deriving DecidableEq, Repr

structure RootEvidence where
  proofLane : LaneOutcome
  refutationLane : LaneOutcome
  proofSha : Option String
  refutationSha : Option String
  finalFailSha : Option String

def Ready (E : RootEvidence) : Prop :=
  (E.proofLane = .proved ∧ E.refutationLane = .failed ∧
    E.proofSha.isSome ∧ E.finalFailSha.isSome) ∨
  (E.refutationLane = .proved ∧ E.proofLane = .failed ∧
    E.refutationSha.isSome ∧ E.finalFailSha.isSome)

def WinningRoot (E : RootEvidence) : Option String :=
  if E.proofLane = .proved ∧ E.refutationLane = .failed then
    E.proofSha
  else if E.refutationLane = .proved ∧ E.proofLane = .failed then
    E.refutationSha
  else
    none

theorem ready_implies_root_present
    (E : RootEvidence)
    (h : Ready E) :
    (WinningRoot E).isSome := by
  rcases h with h | h
  · rcases h with ⟨hp, hr, hs, hff⟩
    simp [WinningRoot, hp, hr, hs]
  · rcases h with ⟨hr, hp, hs, hff⟩
    simp [WinningRoot, hp, hr, hs]

theorem ready_requires_final_fail_sha
    (E : RootEvidence)
    (h : Ready E) :
    E.finalFailSha.isSome := by
  rcases h with h | h
  · exact h.2.2.2
  · exact h.2.2.2

#print axioms ready_implies_root_present
#print axioms ready_requires_final_fail_sha

end NSFinalAssembler
