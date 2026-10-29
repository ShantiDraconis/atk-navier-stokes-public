import Mathlib

/-!
# Navier-Stokes Closed-Form Architecture

Self-contained fail-closed architecture for the proposed closure route.

This file proves the exact logic:
  ActualNS -> subcritical bulk/tail certificate
  -> uniform delta > 0
  -> strict signed depletion
  -> G1-style bridge
  -> global regularity, provided the downstream continuation theorem is supplied.

It does not manufacture the first PDE producer or the downstream continuation theorem.
-/

namespace NSClosedArchitecture

variable {State : Type}

structure Data where
  nu : ℝ
  hnu : 0 < nu
  stretching : State → ℝ → ℝ
  dissipation : State → ℝ → ℝ
  hdissipation : ∀ u t, 0 ≤ dissipation u t

structure BulkTail
    (ActualNS : State → Prop) (D : Data (State := State)) where
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

def StrictSignedDepletion
    (ActualNS : State → Prop) (D : Data (State := State)) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ u, ActualNS u → ∀ t,
      D.stretching u t ≤ (1 - δ) * D.nu * D.dissipation u t

theorem bulk_tail_closes_signed_depletion
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (C : BulkTail ActualNS D) :
    StrictSignedDepletion ActualNS D := by
  let δ : ℝ := 1 - (C.bulkCoeff + C.tailCoeff)
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith [C.subcritical]
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    linarith [C.bulkCoeff_nonneg, C.tailCoeff_nonneg]
  refine ⟨δ, hδpos, hδle, ?_⟩
  intro u hu t
  have hb := C.bulk_bound u hu t
  have ht := C.tail_bound u hu t
  have hs := C.split u hu t
  have hνd : 0 ≤ D.nu * D.dissipation u t :=
    mul_nonneg (le_of_lt D.hnu) (D.hdissipation u t)
  dsimp [δ]
  rw [hs]
  nlinarith

/-- The only genuinely new PDE producer required by this architecture. -/
abbrev ActualNSToBulkTail
    (ActualNS : State → Prop) (D : Data (State := State)) :=
  BulkTail ActualNS D

/-- Abstract G1-style bridge exported by strict signed depletion. -/
structure G1Bridge
    (ActualNS : State → Prop) (D : Data (State := State)) where
  delta : ℝ
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  signed :
    ∀ u, ActualNS u → ∀ t,
      D.stretching u t ≤ (1 - delta) * D.nu * D.dissipation u t

/-- Direct constructor from the analytic certificate to the G1 bridge.
    This stays in Type and therefore does not extract data from a Prop-valued existential. -/
def bulkTail_to_G1
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (C : BulkTail ActualNS D) :
    G1Bridge ActualNS D where
  delta := 1 - (C.bulkCoeff + C.tailCoeff)
  delta_pos := by
    linarith [C.subcritical]
  delta_le_one := by
    linarith [C.bulkCoeff_nonneg, C.tailCoeff_nonneg]
  signed := by
    intro u hu t
    have hb := C.bulk_bound u hu t
    have ht := C.tail_bound u hu t
    have hs := C.split u hu t
    have hνd : 0 ≤ D.nu * D.dissipation u t :=
      mul_nonneg (le_of_lt D.hnu) (D.hdissipation u t)
    rw [hs]
    nlinarith

/-- Closed logical composition from the exact PDE producer to G1. -/
def actualNS_to_G1
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (hPDE : ActualNSToBulkTail ActualNS D) :
    G1Bridge ActualNS D :=
  bulkTail_to_G1 ActualNS D hPDE

/-- Minimal downstream interface: no endpoint is hidden. -/
structure Downstream
    (ActualNS GlobalRegularity : State → Prop)
    (D : Data (State := State)) where
  close :
    G1Bridge ActualNS D →
    ∀ u, ActualNS u → GlobalRegularity u

/-- Fast-path closure: if the genuine G1 bridge is already available,
    BulkTail is not required as an intermediate representation.  Reuse the
    certified downstream consumer directly. -/
theorem g1_closes_if_downstream
    (ActualNS GlobalRegularity : State → Prop)
    (D : Data (State := State))
    (hG1 : G1Bridge ActualNS D)
    (hDown : Downstream ActualNS GlobalRegularity D) :
    ∀ u, ActualNS u → GlobalRegularity u := by
  exact hDown.close hG1

/-- Fast-path closure: once a genuine G1 bridge is available, no BulkTail
    reconstruction is required.  The already-certified downstream consumer
    closes regularity directly from G1. -/
theorem navier_stokes_closed_from_G1
    (ActualNS GlobalRegularity : State → Prop)
    (D : Data (State := State))
    (hG1 : G1Bridge ActualNS D)
    (hDown : Downstream ActualNS GlobalRegularity D) :
    ∀ u, ActualNS u → GlobalRegularity u := by
  exact hDown.close hG1

/-- Full closure theorem for this architecture. -/
theorem navier_stokes_closed_if_producers
    (ActualNS GlobalRegularity : State → Prop)
    (D : Data (State := State))
    (hPDE : ActualNSToBulkTail ActualNS D)
    (hDown : Downstream ActualNS GlobalRegularity D) :
    ∀ u, ActualNS u → GlobalRegularity u := by
  exact hDown.close (actualNS_to_G1 ActualNS D hPDE)

#print axioms bulk_tail_closes_signed_depletion
#print axioms navier_stokes_closed_from_G1
#print axioms g1_closes_if_downstream
#print axioms navier_stokes_closed_if_producers

end NSClosedArchitecture
