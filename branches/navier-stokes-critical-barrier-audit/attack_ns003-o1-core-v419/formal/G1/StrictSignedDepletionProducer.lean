import G1_KAdmissible_to_SignedDepletion
import HypothesesComplete_v3

noncomputable section

namespace MillenniumAudit.NS003

open MillenniumAudit.G1KAdmissible

/--
Kernel-level strict signed depletion producer.

This theorem does not assume an amplitude-invariant fixed delta.
It consumes the exact analytic bulk/tail certificates and the strict
subcritical budget, then produces a uniform signed depletion coefficient.
-/
theorem StrictSignedDepletionProducer
    (ν cBulk δTail : ℝ)
    (hν : 0 ≤ ν)
    (d : EnstrophyData)
    (s : StretchSplit d)
    (hBulk : BulkAbsorption ν cBulk d s)
    (hTail : ExceptionalTailControl ν δTail d s)
    (hBudget : SubcriticalBudget cBulk δTail) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ t, d.stretch t ≤ θ * ν * d.z t :=
  G1bc_bulk_tail_to_signed_depletion
    ν cBulk δTail hν d s hBulk hTail hBudget

/--
Equivalent positive-delta form.  The depletion amount is delta = 1-theta,
which is strictly positive exactly because theta < 1.
-/
theorem StrictSignedDepletionProducer_delta
    (ν cBulk δTail : ℝ)
    (hν : 0 ≤ ν)
    (d : EnstrophyData)
    (s : StretchSplit d)
    (hBulk : BulkAbsorption ν cBulk d s)
    (hTail : ExceptionalTailControl ν δTail d s)
    (hBudget : SubcriticalBudget cBulk δTail) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ t, d.stretch t ≤ (1 - δ) * ν * d.z t := by
  rcases StrictSignedDepletionProducer
      ν cBulk δTail hν d s hBulk hTail hBudget with
    ⟨θ, hθ0, hθ1, hstretch⟩
  refine ⟨1 - θ, by linarith, by linarith, ?_⟩
  intro t
  simpa using hstretch t

/--
No fixed-delta assumption is used: delta is constructed from the certified
bulk/tail budget.  This is the positive replacement for the falsified
amplitude-invariant -> fixed-delta route.
-/
theorem strict_signed_route_uses_budget_not_fixed_delta
    (ν cBulk δTail : ℝ)
    (hν : 0 ≤ ν)
    (d : EnstrophyData)
    (s : StretchSplit d)
    (hBulk : BulkAbsorption ν cBulk d s)
    (hTail : ExceptionalTailControl ν δTail d s)
    (hBudget : SubcriticalBudget cBulk δTail) :
    G1HypothesesV3.GeometricDepletion ν
      { z := d.z, stretch := d.stretch, hz := d.hz } := by
  exact G1HypothesesV3.bulk_tail_to_depletion
    ν cBulk δTail hν
    { z := d.z, stretch := d.stretch, hz := d.hz }
    { bulk := s.bulk, tail := s.tail, split := s.split }
    hBulk hTail hBudget

end MillenniumAudit.NS003
