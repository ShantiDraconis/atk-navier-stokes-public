import Mathlib

/-!
# Navier-Stokes Minimal Claim Core

Kernel-clean, self-contained theorem.

CLAIM BOUNDARY:
This file proves only:
  uniform bulk absorption
+ uniform tail absorption
+ total coefficient < 1
=> one uniform strict signed-depletion margin delta > 0.

It does NOT prove that every actual 3D Navier-Stokes solution satisfies the
bulk/tail hypotheses. Therefore this file alone is not an unconditional proof
of global regularity.
-/

namespace NSMinimalClaim

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

#print axioms bulk_tail_closes_signed_depletion

end NSMinimalClaim
