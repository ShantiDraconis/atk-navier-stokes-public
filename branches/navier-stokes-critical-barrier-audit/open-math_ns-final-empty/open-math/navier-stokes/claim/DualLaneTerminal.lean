import Mathlib

namespace NSDualLaneTerminal

inductive LaneOutcome where
  | openMath
  | proved
  | failed
  deriving DecidableEq, Repr

structure ScientificState where
  proofClosed : Prop
  proofFailed : Prop
  refutationClosed : Prop
  refutationFailed : Prop

def FinalFail (S : ScientificState) : Prop :=
  (S.proofClosed ∧ S.refutationFailed) ∨
  (S.refutationClosed ∧ S.proofFailed)

def ScientificallyConsistent (S : ScientificState) : Prop :=
  ¬ (S.proofClosed ∧ S.proofFailed) ∧
  ¬ (S.refutationClosed ∧ S.refutationFailed)

structure TerminalEvidence where
  proofLane : LaneOutcome
  refutationLane : LaneOutcome
  proofSha : Option String
  refutationSha : Option String
  finalFailSha : Option String

def Ready (S : ScientificState) (E : TerminalEvidence) : Prop :=
  ((S.proofClosed ∧ S.refutationFailed) ∧
    E.proofLane = .proved ∧ E.refutationLane = .failed ∧
    E.proofSha.isSome = true ∧ E.finalFailSha.isSome = true) ∨
  ((S.refutationClosed ∧ S.proofFailed) ∧
    E.refutationLane = .proved ∧ E.proofLane = .failed ∧
    E.refutationSha.isSome = true ∧ E.finalFailSha.isSome = true)

def WinningRoot (E : TerminalEvidence) : Option String :=
  if E.proofLane = .proved then
    if E.refutationLane = .failed then E.proofSha else none
  else if E.refutationLane = .proved then
    if E.proofLane = .failed then E.refutationSha else none
  else none

def proofTerminal
    (proofSha finalFailSha : String) : TerminalEvidence where
  proofLane := .proved
  refutationLane := .failed
  proofSha := some proofSha
  refutationSha := none
  finalFailSha := some finalFailSha

def refutationTerminal
    (refutationSha finalFailSha : String) : TerminalEvidence where
  proofLane := .failed
  refutationLane := .proved
  proofSha := none
  refutationSha := some refutationSha
  finalFailSha := some finalFailSha

theorem proof_terminal_ready
    (S : ScientificState)
    (hProof : S.proofClosed)
    (hRefFail : S.refutationFailed)
    (proofSha finalFailSha : String) :
    Ready S (proofTerminal proofSha finalFailSha) := by
  left
  exact ⟨⟨hProof, hRefFail⟩, rfl, rfl, rfl, rfl⟩

theorem refutation_terminal_ready
    (S : ScientificState)
    (hRef : S.refutationClosed)
    (hProofFail : S.proofFailed)
    (refutationSha finalFailSha : String) :
    Ready S (refutationTerminal refutationSha finalFailSha) := by
  right
  exact ⟨⟨hRef, hProofFail⟩, rfl, rfl, rfl, rfl⟩

theorem ready_implies_final_fail
    (S : ScientificState)
    (E : TerminalEvidence)
    (h : Ready S E) :
    FinalFail S := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem ready_implies_root_present
    (S : ScientificState)
    (E : TerminalEvidence)
    (h : Ready S E) :
    (WinningRoot E).isSome = true := by
  rcases h with h | h
  · rcases h with ⟨_, hep, her, hs, _⟩
    simp [WinningRoot, hep, her, hs]
  · rcases h with ⟨_, her, hep, hs, _⟩
    simp [WinningRoot, her, hep, hs]

def openState : ScientificState where
  proofClosed := False
  proofFailed := False
  refutationClosed := False
  refutationFailed := False

def openEvidence : TerminalEvidence where
  proofLane := .openMath
  refutationLane := .openMath
  proofSha := none
  refutationSha := none
  finalFailSha := none

theorem open_open_not_ready :
    ¬ Ready openState openEvidence := by
  simp [Ready, openState, openEvidence]

theorem open_open_no_final_fail :
    ¬ FinalFail openState := by
  simp [FinalFail, openState]

theorem open_open_no_root :
    WinningRoot openEvidence = none := by
  simp [WinningRoot, openEvidence]


/-- Semantic meeting point for the two lanes.  If closing the proof lane entails
    regularity of every actual NS state, while closing the refutation lane
    entails an actual irregular state, both lanes cannot be scientifically
    closed at once. -/
theorem proof_and_refutation_closed_contradict
    {State : Type}
    (ActualNS regular : State → Prop)
    (S : ScientificState)
    (hProofSem :
      S.proofClosed → ∀ u, ActualNS u → regular u)
    (hRefSem :
      S.refutationClosed → ∃ u, ActualNS u ∧ ¬ regular u) :
    ¬ (S.proofClosed ∧ S.refutationClosed) := by
  intro hboth
  rcases hboth with ⟨hp, hr⟩
  rcases hRefSem hr with ⟨u, hu, hirreg⟩
  exact hirreg (hProofSem hp u hu)

#print axioms proof_terminal_ready
#print axioms proof_and_refutation_closed_contradict
#print axioms refutation_terminal_ready
#print axioms ready_implies_final_fail
#print axioms ready_implies_root_present
#print axioms open_open_not_ready
#print axioms open_open_no_final_fail
#print axioms open_open_no_root

end NSDualLaneTerminal
