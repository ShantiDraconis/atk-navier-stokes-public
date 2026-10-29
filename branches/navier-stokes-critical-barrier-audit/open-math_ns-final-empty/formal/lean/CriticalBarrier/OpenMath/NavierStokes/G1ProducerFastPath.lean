import Mathlib

namespace NSG1ProducerFastPath

variable {State : Type}

/-- Minimal scientific producer contract for the proof lane.

This file intentionally contains no Navier--Stokes theorem.  It isolates the
single object that, once genuinely constructed from the actual 3D
incompressible NSE, unlocks the already-certified downstream chain. -/
structure Data where
  nu : ℝ
  hnu : 0 < nu
  stretching : State → ℝ → ℝ
  dissipation : State → ℝ → ℝ
  hdissipation : ∀ u t, 0 ≤ dissipation u t

structure G1Producer
    (ActualNS : State → Prop)
    (D : Data (State := State)) where
  delta : ℝ
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  signed :
    ∀ u, ActualNS u → ∀ t,
      D.stretching u t ≤ (1 - delta) * D.nu * D.dissipation u t

/-- Exact proposition-level target exported for audits and certificates. -/
def G1Closed
    (ActualNS : State → Prop)
    (D : Data (State := State)) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
    ∀ u, ActualNS u → ∀ t,
      D.stretching u t ≤ (1 - delta) * D.nu * D.dissipation u t

theorem producer_implies_closed
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (P : G1Producer ActualNS D) :
    G1Closed ActualNS D := by
  exact ⟨P.delta, P.delta_pos, P.delta_le_one, P.signed⟩

/-- Bulk/tail is only one possible construction route. -/
structure BulkTailProducer
    (ActualNS : State → Prop)
    (D : Data (State := State)) where
  bulkCoeff : ℝ
  tailCoeff : ℝ
  bulkCoeff_nonneg : 0 ≤ bulkCoeff
  tailCoeff_nonneg : 0 ≤ tailCoeff
  subcritical : bulkCoeff + tailCoeff < 1
  bulk : State → ℝ → ℝ
  tail : State → ℝ → ℝ
  split :
    ∀ u, ActualNS u → ∀ t,
      D.stretching u t = bulk u t + tail u t
  bulk_bound :
    ∀ u, ActualNS u → ∀ t,
      bulk u t ≤ bulkCoeff * D.nu * D.dissipation u t
  tail_bound :
    ∀ u, ActualNS u → ∀ t,
      tail u t ≤ tailCoeff * D.nu * D.dissipation u t

def bulkTail_to_G1Producer
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (B : BulkTailProducer ActualNS D) :
    G1Producer ActualNS D where
  delta := 1 - (B.bulkCoeff + B.tailCoeff)
  delta_pos := by
    linarith [B.subcritical]
  delta_le_one := by
    linarith [B.bulkCoeff_nonneg, B.tailCoeff_nonneg]
  signed := by
    intro u hu t
    have hb := B.bulk_bound u hu t
    have ht := B.tail_bound u hu t
    have hs := B.split u hu t
    have hνd : 0 ≤ D.nu * D.dissipation u t :=
      mul_nonneg (le_of_lt D.hnu) (D.hdissipation u t)
    rw [hs]
    nlinarith

/-- Fail-closed: the interface itself has no default/vacuous producer. -/
def ProducerExists
    (ActualNS : State → Prop)
    (D : Data (State := State)) : Prop :=
  Nonempty (G1Producer ActualNS D)

theorem bulkTail_implies_producer_exists
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (B : BulkTailProducer ActualNS D) :
    ProducerExists ActualNS D :=
  ⟨bulkTail_to_G1Producer ActualNS D B⟩

#print axioms producer_implies_closed
#print axioms bulkTail_to_G1Producer
#print axioms bulkTail_implies_producer_exists

end NSG1ProducerFastPath
