import Mathlib

namespace CriticalBarrier.ScientificMeet

inductive EvidenceState where
  | unknown
  | proved
  | disproved
  deriving DecidableEq, Repr

inductive MeetState where
  | openMath
  | proofOnly
  | refutationOnly
  | neither
  | conflict
  deriving DecidableEq, Repr

def meet : EvidenceState → EvidenceState → MeetState
  | .proved,    .proved    => .conflict
  | .proved,    .disproved => .proofOnly
  | .disproved, .proved    => .refutationOnly
  | .disproved, .disproved => .neither
  | _,          _          => .openMath

@[simp] theorem meet_proved_proved :
    meet .proved .proved = .conflict := rfl

@[simp] theorem meet_proved_disproved :
    meet .proved .disproved = .proofOnly := rfl

@[simp] theorem meet_disproved_proved :
    meet .disproved .proved = .refutationOnly := rfl

@[simp] theorem meet_disproved_disproved :
    meet .disproved .disproved = .neither := rfl

@[simp] theorem meet_unknown_left (r : EvidenceState) :
    meet .unknown r = .openMath := by
  cases r <;> rfl

@[simp] theorem meet_unknown_right (p : EvidenceState) :
    meet p .unknown = .openMath := by
  cases p <;> rfl

def CanIssueScientificFinal : MeetState → Prop
  | .proofOnly      => True
  | .refutationOnly => True
  | .openMath       => False
  | .neither        => False
  | .conflict       => False

@[simp] theorem conflict_cannot_issue :
    ¬ CanIssueScientificFinal .conflict := by
  simp [CanIssueScientificFinal]

@[simp] theorem openMath_cannot_issue :
    ¬ CanIssueScientificFinal .openMath := by
  simp [CanIssueScientificFinal]

@[simp] theorem neither_cannot_issue :
    ¬ CanIssueScientificFinal .neither := by
  simp [CanIssueScientificFinal]

end CriticalBarrier.ScientificMeet
