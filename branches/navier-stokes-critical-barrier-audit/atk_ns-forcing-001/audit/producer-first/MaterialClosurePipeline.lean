/-!
# MaterialClosurePipeline

Forward-only, proof-escape-free continuation of the frozen producer-first core.

This file does not assert Navier--Stokes regularity.  It compresses the
remaining material PDE obligation into an explicit three-piece stretching
decomposition and proves that such a decomposition produces the already
certified `ActualNSToSignedGainCore`.

CI checks this file only after concatenating:
1. ProducerFirst.lean
2. SignedGainCore.lean
3. MaterialClosurePipeline.lean

No axiom, sorry, admit, endpoint placeholder, or equivalent regularity
assumption is introduced here.
-/

noncomputable section

namespace NSProducerFirst

/--
Canonical three-piece material witness over the exact producer-first
`EnstrophyData`.

The witness retains exactly the inequalities needed to produce
`SignedGainCore`:

  stretch = bulk + tail + remainder
  bulk <= cBulk * nu * z
  tail <= cTail * nu * z
  remainder <= C * y^2
  cBulk + cTail < 1

This is a canonicalized producer-first version of the richer
`QuadraticBulkTailRemainder` route already present in
`FlexibleBulkTailMaterialOperator.lean`; it avoids reopening the historical
G1 representation layer.
-/
structure QuadraticBulkTailWitness
    (ν : ℝ)
    (d : EnstrophyData) where
  bulk : ℝ → ℝ
  tail : ℝ → ℝ
  remainder : ℝ → ℝ

  cBulk : ℝ
  cTail : ℝ
  C : ℝ

  cBulk_nonneg : 0 ≤ cBulk
  cTail_nonneg : 0 ≤ cTail
  budget : cBulk + cTail < 1

  split :
    ∀ t, d.stretch t = bulk t + tail t + remainder t

  bulk_bound :
    ∀ t, bulk t ≤ cBulk * ν * d.z t

  tail_bound :
    ∀ t, tail t ≤ cTail * ν * d.z t

  remainder_bound :
    ∀ t, remainder t ≤ C * (d.y t)^2

/--
A genuine quadratic bulk/tail witness immediately gives the already frozen
minimal signed-gain core.  This theorem contains no Navier--Stokes hypothesis
other than the supplied material witness itself; its purpose is exact
composition, not endpoint promotion.
-/
def QuadraticBulkTailWitness.toSignedGainCore
    {ν : ℝ}
    {d : EnstrophyData}
    (H : QuadraticBulkTailWitness ν d) :
    SignedGainCore ν d where
  theta := H.cBulk + H.cTail
  C := H.C
  htheta1 := H.budget
  stretching := by
    intro t
    rw [H.split t]
    have hb := H.bulk_bound t
    have ht := H.tail_bound t
    have hr := H.remainder_bound t
    nlinarith

/--
Exact genuine-dynamics frontier in decomposition form.

This is not a replacement target: the next definition proves that inhabiting
this type constructs the canonical `ActualNSToSignedGainCore`.
-/
def ActualNSToQuadraticBulkTailWitness
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Type :=
  (u : State) → ActualNS u → QuadraticBulkTailWitness ν (data u)

/--
Forward-only projection into the frozen canonical frontier.
-/
def actualNSToSignedGainCore_of_quadraticBulkTail
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (P : ActualNSToQuadraticBulkTailWitness State ActualNS ν data) :
    ActualNSToSignedGainCore State ActualNS ν data :=
  fun u hu => (P u hu).toSignedGainCore

/--
Forward-only projection all the way to the previously certified full
`SignedGainCertificate` producer, reusing `actualNSToSignedGain_of_core`.
-/
def actualNSToSignedGain_of_quadraticBulkTail
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (hν : 0 ≤ ν)
    (P : ActualNSToQuadraticBulkTailWitness State ActualNS ν data) :
    ActualNSToSignedGain State ActualNS ν data :=
  actualNSToSignedGain_of_core hν
    (actualNSToSignedGainCore_of_quadraticBulkTail P)

/--
Nonempty-level promotion used by the fail-closed gate.  It proves only the
logical projection from a genuine decomposition producer to the frozen core.
-/
theorem nonempty_actualNSToSignedGainCore_of_quadraticBulkTail
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (h :
      Nonempty
        (ActualNSToQuadraticBulkTailWitness State ActualNS ν data)) :
    Nonempty (ActualNSToSignedGainCore State ActualNS ν data) := by
  rcases h with ⟨P⟩
  exact ⟨actualNSToSignedGainCore_of_quadraticBulkTail P⟩

/--
The old strict two-piece route embeds into the quadratic route with
`remainder = 0` and `C = 0`.  This preserves the already certified
`actualNSToSignedGainCore_of_bulkTail` path while giving one canonical
frontier representation.
-/
def quadraticBulkTailWitness_of_strict
    {ν : ℝ}
    {d : EnstrophyData}
    (bulk tail : ℝ → ℝ)
    (split : ∀ t, d.stretch t = bulk t + tail t)
    (cBulk cTail : ℝ)
    (hBulk0 : 0 ≤ cBulk)
    (hTail0 : 0 ≤ cTail)
    (hBulk : ∀ t, bulk t ≤ cBulk * ν * d.z t)
    (hTail : ∀ t, tail t ≤ cTail * ν * d.z t)
    (hBudget : cBulk + cTail < 1) :
    QuadraticBulkTailWitness ν d where
  bulk := bulk
  tail := tail
  remainder := fun _ => 0
  cBulk := cBulk
  cTail := cTail
  C := 0
  cBulk_nonneg := hBulk0
  cTail_nonneg := hTail0
  budget := hBudget
  split := by
    intro t
    rw [split t]
    ring
  bulk_bound := hBulk
  tail_bound := hTail
  remainder_bound := by
    intro t
    simp

#print axioms NSProducerFirst.QuadraticBulkTailWitness.toSignedGainCore
#print axioms NSProducerFirst.actualNSToSignedGainCore_of_quadraticBulkTail
#print axioms NSProducerFirst.actualNSToSignedGain_of_quadraticBulkTail
#print axioms NSProducerFirst.nonempty_actualNSToSignedGainCore_of_quadraticBulkTail
#print axioms NSProducerFirst.quadraticBulkTailWitness_of_strict

end NSProducerFirst
