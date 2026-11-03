import Mathlib

/-!
# Bulk/Tail terminal obligation for the Navier-Stokes route

This file isolates the only non-certified analytic producer.

Provenance is explicit: this obligation feeds the Navier-Stokes closure route.
The file contains no proof escape and no hidden regularity hypothesis.

Uniformity is only in time. The strict constant `cStar` may depend on the
particular solution / initial datum represented by `u`.
-/

namespace NSBulkTailTerminal

variable {State : Type}

structure Data where
  nu : ℝ
  hnu : 0 < nu
  stretching : State → ℝ → ℝ
  dissipation : State → ℝ → ℝ
  hdissipation : ∀ u t, 0 ≤ dissipation u t

/-- Per-solution bulk/tail certificate. Coefficients may vary in time, but their
sum is dominated by one solution-dependent constant strictly below one. -/
structure BulkTailProducer
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (u : State) where
  bulkCoeff : ℝ → ℝ
  tailCoeff : ℝ → ℝ
  cStar : ℝ
  cStar_nonneg : 0 ≤ cStar
  cStar_lt_one : cStar < 1
  bulkCoeff_nonneg : ∀ t, 0 ≤ bulkCoeff t
  tailCoeff_nonneg : ∀ t, 0 ≤ tailCoeff t
  budget : ∀ t, bulkCoeff t + tailCoeff t ≤ cStar
  bulk : ℝ → ℝ
  tail : ℝ → ℝ
  split :
    ActualNS u →
    ∀ t, D.stretching u t = bulk t + tail t
  bulk_bound :
    ActualNS u →
    ∀ t, bulk t ≤ bulkCoeff t * D.nu * D.dissipation u t
  tail_bound :
    ActualNS u →
    ∀ t, tail t ≤ tailCoeff t * D.nu * D.dissipation u t

/-- The unique OPEN_MATH target. -/
def BulkTailOpenMath
    (ActualNS : State → Prop)
    (D : Data (State := State)) : Prop :=
  ∀ u, ActualNS u → Nonempty (BulkTailProducer ActualNS D u)

/-- Closed algebra after a producer exists. The margin depends on the solution
but is uniform in time. -/
theorem producer_implies_uniform_margin
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (u : State)
    (hu : ActualNS u)
    (P : BulkTailProducer ActualNS D u) :
    ∃ δ : ℝ,
      0 < δ ∧
      δ ≤ 1 ∧
      ∀ t,
        D.stretching u t ≤
          (1 - δ) * D.nu * D.dissipation u t := by
  let δ : ℝ := 1 - P.cStar
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith [P.cStar_lt_one]
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    linarith [P.cStar_nonneg]
  refine ⟨δ, hδpos, hδle, ?_⟩
  intro t
  have hb := P.bulk_bound hu t
  have ht := P.tail_bound hu t
  have hbudget := P.budget t
  have hs := P.split hu t
  have hνd : 0 ≤ D.nu * D.dissipation u t :=
    mul_nonneg (le_of_lt D.hnu) (D.hdissipation u t)
  dsimp [δ]
  rw [hs]
  nlinarith

/-- Exact strict-budget formulation of the mathematical frontier. -/
def BulkTailStrictBudget
    (ActualNS : State → Prop)
    (D : Data (State := State)) : Prop :=
  ∀ u, ActualNS u →
    ∃ cStar : ℝ,
      cStar < 1 ∧
      ∃ bulkCoeff tailCoeff : ℝ → ℝ,
        (∀ t, 0 ≤ bulkCoeff t) ∧
        (∀ t, 0 ≤ tailCoeff t) ∧
        (∀ t, bulkCoeff t + tailCoeff t ≤ cStar)

/-- Any full producer immediately exposes the strict-budget theorem. -/
theorem openMath_implies_strict_budget
    (ActualNS : State → Prop)
    (D : Data (State := State))
    (h : BulkTailOpenMath ActualNS D) :
    BulkTailStrictBudget ActualNS D := by
  intro u hu
  rcases h u hu with ⟨P⟩
  exact ⟨P.cStar, P.cStar_lt_one, P.bulkCoeff, P.tailCoeff,
    P.bulkCoeff_nonneg, P.tailCoeff_nonneg, P.budget⟩

#print axioms producer_implies_uniform_margin
#print axioms openMath_implies_strict_budget

end NSBulkTailTerminal
