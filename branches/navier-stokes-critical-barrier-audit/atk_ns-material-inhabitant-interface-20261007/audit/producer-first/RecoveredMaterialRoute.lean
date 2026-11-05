/-!
Recovered material route for the canonical producer-first Navier--Stokes lane.

This file consolidates proof fragments that already existed in the repository
under the bulk/tail signed-depletion program and aligns them with the exact
current terminal target SignedGainCore.

No axiom, sorry, admit, or hidden ActualNS assumption is introduced.
-/

noncomputable section

namespace NSProducerFirst

/-- Exact three-way decomposition of vortex stretching. -/
structure MaterialStretchSplit (d : EnstrophyData) where
  bulk : ℝ → ℝ
  tail : ℝ → ℝ
  remainder : ℝ → ℝ
  split :
    ∀ t, d.stretch t = bulk t + tail t + remainder t

/-- Complete pointwise material estimates needed by the recovered route. -/
structure BulkTailRemainderBounds
    (ν : ℝ)
    (d : EnstrophyData)
    (s : MaterialStretchSplit d) where
  cBulk : ℝ
  cTail : ℝ
  C : ℝ
  hcBulk : 0 ≤ cBulk
  hcTail : 0 ≤ cTail
  hC : 0 ≤ C
  hbudget : cBulk + cTail < 1
  bulk_bound :
    ∀ t, s.bulk t ≤ cBulk * ν * d.z t
  tail_bound :
    ∀ t, s.tail t ≤ cTail * ν * d.z t
  remainder_bound :
    ∀ t, s.remainder t ≤ C * (d.y t)^2

/-- Recovered algebraic closure:
bulk absorption + tail absorption + quadratic remainder + strict total
viscous budget construct the exact SignedGainCore target. -/
def bulkTailRemainder_to_signedGainCore
    {ν : ℝ}
    {d : EnstrophyData}
    (s : MaterialStretchSplit d)
    (h : BulkTailRemainderBounds ν d s) :
    SignedGainCore ν d where
  theta := h.cBulk + h.cTail
  C := h.C
  htheta1 := h.hbudget
  stretching := by
    intro t
    have hb := h.bulk_bound t
    have ht := h.tail_bound t
    have hr := h.remainder_bound t
    rw [s.split t]
    calc
      s.bulk t + s.tail t + s.remainder t
          ≤ (h.cBulk * ν * d.z t) +
              (h.cTail * ν * d.z t) +
              h.C * (d.y t)^2 := by
            exact add_le_add (add_le_add hb ht) hr
      _ = (h.cBulk + h.cTail) * ν * d.z t +
            h.C * (d.y t)^2 := by
            ring

/-- Actual-NS material producer decomposed into the exact local estimates.
This is a stronger audit surface than directly postulating SignedGainCore:
every coefficient and every pointwise estimate is visible. -/
structure ActualNSBulkTailRemainder
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) where
  split :
    ∀ u : State, ActualNS u → MaterialStretchSplit (data u)
  bounds :
    ∀ u : State, ∀ hu : ActualNS u,
      BulkTailRemainderBounds ν (data u) (split u hu)

/-- Once the recovered bulk/tail/remainder payload is genuinely proved for
actual NS states, the canonical terminal producer follows definitionally. -/
def actualNSToSignedGainCore_of_bulkTailRemainder
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (P : ActualNSBulkTailRemainder State ActualNS ν data) :
    ActualNSToSignedGainCore State ActualNS ν data :=
  fun u hu =>
    bulkTailRemainder_to_signedGainCore
      (P.split u hu)
      (P.bounds u hu)

/-- Exact equivalence in the forward direction used by the audit:
a recovered material decomposition is sufficient for the canonical material
inhabitant. -/
def materialInhabitant_of_bulkTailRemainder
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (P : ActualNSBulkTailRemainder State ActualNS ν data) :
    NSMaterialInhabitant State ActualNS ν data :=
  actualNSToSignedGainCore_of_bulkTailRemainder P

/-- Audit decomposition of the remaining mathematics.  A constructor for this
structure is the exact place where the genuine PDE proof must live. -/
def RemainingMaterialObligation
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Type :=
  ActualNSBulkTailRemainder State ActualNS ν data

theorem recovered_route_is_sufficient
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData} :
    Nonempty (RemainingMaterialObligation State ActualNS ν data) →
    Nonempty (NSMaterialInhabitant State ActualNS ν data) := by
  rintro ⟨P⟩
  exact ⟨materialInhabitant_of_bulkTailRemainder P⟩


/-- Historical strict bulk/tail producer recovered from
atk/ns-bulk-tail-material-producer-20261001.  This is the exact C=0 route that
was previously separated from the canonical producer-first endpoint. -/
structure RecoveredActualNSBulkTailProducer
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) where
  cBulk : ℝ
  deltaTail : ℝ
  hNu : 0 ≤ ν
  hcBulk : 0 ≤ cBulk
  hdeltaTail : 0 ≤ deltaTail
  budget : cBulk + deltaTail < 1
  split :
    ∀ u : State, ActualNS u → MaterialStretchSplit (data u)
  bulk :
    ∀ u (hu : ActualNS u), ∀ t,
      (split u hu).bulk t ≤ cBulk * ν * (data u).z t
  tail :
    ∀ u (hu : ActualNS u), ∀ t,
      (split u hu).tail t ≤ deltaTail * ν * (data u).z t
  remainder_zero :
    ∀ u (hu : ActualNS u), ∀ t,
      (split u hu).remainder t = 0

/-- The recovered historical C=0 producer is sufficient for the current
canonical SignedGainCore. -/
def RecoveredActualNSBulkTailProducer.toSignedGainCore
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (P : RecoveredActualNSBulkTailProducer State ActualNS ν data) :
    ActualNSToSignedGainCore State ActualNS ν data := by
  intro u hu
  let s := P.split u hu
  refine
    { theta := P.cBulk + P.deltaTail
      C := 0
      htheta1 := P.budget
      stretching := ?_ }
  intro t
  have hs := s.split t
  have hb := P.bulk u hu t
  have ht := P.tail u hu t
  have hr := P.remainder_zero u hu t
  dsimp [s] at hs hb ht hr
  rw [hs, hr]
  calc
    (P.split u hu).bulk t + (P.split u hu).tail t + 0
        ≤ P.cBulk * ν * (data u).z t +
          P.deltaTail * ν * (data u).z t + 0 := by
            exact add_le_add (add_le_add hb ht) (le_refl 0)
    _ = (P.cBulk + P.deltaTail) * ν * (data u).z t +
          0 * ((data u).y t)^2 := by
            ring

/-- Recovered historical terminal statement, now represented as a Type rather
than a free Prop wrapper. -/
def NS_BULK_TAIL_RECOVERED_OPEN_MATH
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Type :=
  RecoveredActualNSBulkTailProducer State ActualNS ν data

theorem recovered_bulk_tail_closes_material
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData} :
    Nonempty (NS_BULK_TAIL_RECOVERED_OPEN_MATH State ActualNS ν data) →
    Nonempty (NSMaterialInhabitant State ActualNS ν data) := by
  rintro ⟨P⟩
  exact ⟨P.toSignedGainCore⟩

end NSProducerFirst
