import Mathlib

/-!
# Minimal GREEN core for Navier-Stokes OPEN_MATH

This theorem is intentionally the strongest result that can be made kernel-GREEN
without fabricating the unresolved PDE implication.

It proves that a uniform bulk/tail absorption budget strictly below viscosity
produces one global positive depletion margin delta.

It does NOT prove that ActualNS supplies those bulk/tail estimates.
-/

namespace CriticalBarrier.OpenMath.NavierStokes.MinimalGreen

variable {State : Type}

structure PDEData where
  nu : ℝ
  hnu : 0 < nu
  stretching : State → ℝ → ℝ
  z : State → ℝ → ℝ
  hz : ∀ u t, 0 ≤ z u t

structure UniformBulkTailCertificate
    (ActualNS : State → Prop) (D : PDEData (State := State)) where
  cBulk : ℝ
  cTail : ℝ
  cBulk_nonneg : 0 ≤ cBulk
  cTail_nonneg : 0 ≤ cTail
  budget : cBulk + cTail < 1
  bulk : State → ℝ → ℝ
  tail : State → ℝ → ℝ
  split :
    ∀ u, ActualNS u → ∀ t,
      D.stretching u t = bulk u t + tail u t
  bulk_bound :
    ∀ u, ActualNS u → ∀ t,
      bulk u t ≤ cBulk * D.nu * D.z u t
  tail_bound :
    ∀ u, ActualNS u → ∀ t,
      tail u t ≤ cTail * D.nu * D.z u t

/-- Exact strict signed-depletion conclusion from the uniform analytic budget. -/
theorem uniform_bulk_tail_implies_strict_signed_depletion
    (ActualNS : State → Prop)
    (D : PDEData (State := State))
    (C : UniformBulkTailCertificate ActualNS D) :
    ∃ δ : ℝ,
      0 < δ ∧
      δ ≤ 1 ∧
      ∀ u, ActualNS u → ∀ t,
        D.stretching u t ≤ (1 - δ) * D.nu * D.z u t := by
  let δ : ℝ := 1 - (C.cBulk + C.cTail)
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith [C.budget]
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    linarith [C.cBulk_nonneg, C.cTail_nonneg]
  refine ⟨δ, hδpos, hδle, ?_⟩
  intro u hu t
  have hb := C.bulk_bound u hu t
  have ht := C.tail_bound u hu t
  have hs := C.split u hu t
  have hνz : 0 ≤ D.nu * D.z u t :=
    mul_nonneg (le_of_lt D.hnu) (D.hz u t)
  dsimp [δ]
  rw [hs]
  nlinarith

end CriticalBarrier.OpenMath.NavierStokes.MinimalGreen
