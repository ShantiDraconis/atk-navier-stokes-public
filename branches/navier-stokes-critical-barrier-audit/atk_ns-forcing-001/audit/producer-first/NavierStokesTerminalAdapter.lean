/-!
NS-FORCING-001 / terminal parameter adapter.

Intended concatenation order:
1. audit/producer-first/ProducerFirst.lean
2. audit/producer-first/SignedGainCore.lean
3. audit/producer-first/MaterialClosurePipeline.lean
4. this file

No proof escape or endpoint regularity assumption is introduced here.
-/

noncomputable section

namespace NSProducerFirst

def NavierStokesMaterialCertifies
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Prop :=
  Nonempty (ActualNSToSignedGainCore State ActualNS ν data)

def NavierStokesMaterialRefutes
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Prop :=
  IsEmpty (ActualNSToSignedGainCore State ActualNS ν data)

def NavierStokesQuadraticProducer
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Prop :=
  Nonempty (ActualNSToQuadraticBulkTailWitness State ActualNS ν data)

theorem quadraticProducer_certifies_navierStokesMaterial
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (h : NavierStokesQuadraticProducer State ActualNS ν data) :
    NavierStokesMaterialCertifies State ActualNS ν data :=
  nonempty_actualNSToSignedGainCore_of_quadraticBulkTail h

theorem not_navierStokesMaterialCertifies_iff_refutes
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) :
    ¬ NavierStokesMaterialCertifies State ActualNS ν data ↔
      NavierStokesMaterialRefutes State ActualNS ν data := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro P
    exact h ⟨P⟩
  · intro h hcert
    rcases hcert with ⟨P⟩
    exact h.false P

theorem navierStokes_material_cert_refute_disjoint
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) :
    ¬ (NavierStokesMaterialCertifies State ActualNS ν data ∧
       NavierStokesMaterialRefutes State ActualNS ν data) := by
  rintro ⟨⟨P⟩, hE⟩
  exact hE.false P

#print axioms NSProducerFirst.quadraticProducer_certifies_navierStokesMaterial
#print axioms NSProducerFirst.not_navierStokesMaterialCertifies_iff_refutes
#print axioms NSProducerFirst.navierStokes_material_cert_refute_disjoint

end NSProducerFirst
