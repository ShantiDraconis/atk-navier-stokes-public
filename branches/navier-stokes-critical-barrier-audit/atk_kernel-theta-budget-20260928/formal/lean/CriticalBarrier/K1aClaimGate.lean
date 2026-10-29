import CriticalBarrier.K1aXiEpsAlgebra
import CriticalBarrier.ScientificMeet

namespace CriticalBarrier.K1aClaimGate

open CriticalBarrier.ScientificMeet

structure LaneEvidence where
  proofLane : EvidenceState
  refutationLane : EvidenceState

def state (e : LaneEvidence) : MeetState :=
  meet e.proofLane e.refutationLane

def claimable (e : LaneEvidence) : Prop :=
  CanIssueScientificFinal (state e)

theorem unknown_proof_blocks_claim (r : EvidenceState) :
    ¬ claimable ⟨.unknown, r⟩ := by
  cases r <;> simp [claimable, state, meet, CanIssueScientificFinal]

theorem unknown_refutation_blocks_claim (p : EvidenceState) :
    ¬ claimable ⟨p, .unknown⟩ := by
  cases p <;> simp [claimable, state, meet, CanIssueScientificFinal]

theorem conflicting_evidence_blocks_claim :
    ¬ claimable ⟨.proved, .proved⟩ := by
  simp [claimable, state, meet, CanIssueScientificFinal]

end CriticalBarrier.K1aClaimGate
