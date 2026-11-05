/-!
Forward-only continuation of audit/producer-first/ProducerFirst.lean.

CI compiles this file by concatenating it after the certified ProducerFirst
source, preserving the frozen source byte-for-byte while kernel-checking this
reduction against its exact canonical declarations.
-/

noncomputable section

namespace NSProducerFirst

/-- Minimal signed-gain core.  The nonnegativity side conditions on theta and C
are not retained here: for nonnegative viscosity they can be normalized by max
without weakening the stretching inequality. -/
structure SignedGainCore (ν : ℝ) (d : EnstrophyData) where
  theta : ℝ
  C : ℝ
  htheta1 : theta < 1
  stretching :
    ∀ t, d.stretch t ≤ theta * ν * d.z t + C * (d.y t)^2

/-- For nonnegative viscosity, every core witness can be normalized to the
full fail-closed SignedGainCertificate by replacing theta and C with their
nonnegative parts. -/
def SignedGainCore.toCertificate
    {ν : ℝ} {d : EnstrophyData}
    (hν : 0 ≤ ν)
    (h : SignedGainCore ν d) :
    SignedGainCertificate ν d where
  theta := max h.theta 0
  C := max h.C 0
  htheta0 := le_max_right _ _
  htheta1 := max_lt h.htheta1 (by norm_num)
  hC := le_max_right _ _
  stretching := by
    intro t
    have hνz : 0 ≤ ν * d.z t := mul_nonneg hν (d.hz t)
    have hy2 : 0 ≤ (d.y t)^2 := sq_nonneg (d.y t)
    have hθ :
        h.theta * (ν * d.z t) ≤
          max h.theta 0 * (ν * d.z t) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hνz
    have hC' :
        h.C * (d.y t)^2 ≤
          max h.C 0 * (d.y t)^2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hy2
    calc
      d.stretch t
          ≤ h.theta * ν * d.z t + h.C * (d.y t)^2 :=
        h.stretching t
      _ = h.theta * (ν * d.z t) + h.C * (d.y t)^2 := by
        ring
      _ ≤ max h.theta 0 * (ν * d.z t) +
            max h.C 0 * (d.y t)^2 :=
        add_le_add hθ hC'
      _ = max h.theta 0 * ν * d.z t +
            max h.C 0 * (d.y t)^2 := by
        ring

/-- Forgetting the nonnegativity bookkeeping gives the core immediately. -/
def SignedGainCertificate.toCore
    {ν : ℝ} {d : EnstrophyData}
    (h : SignedGainCertificate ν d) :
    SignedGainCore ν d where
  theta := h.theta
  C := h.C
  htheta1 := h.htheta1
  stretching := h.stretching

/-- At positive/nonnegative viscosity, inhabiting the old certificate is
equivalent to inhabiting the smaller core. -/
theorem nonempty_signedGainCertificate_iff_core
    {ν : ℝ} {d : EnstrophyData}
    (hν : 0 ≤ ν) :
    Nonempty (SignedGainCertificate ν d) ↔
      Nonempty (SignedGainCore ν d) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.toCore⟩
  · rintro ⟨h⟩
    exact ⟨h.toCertificate hν⟩

/-- Producer-first map with only the material signed inequality retained. -/
def ActualNSToSignedGainCore
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Type :=
  (u : State) → ActualNS u → SignedGainCore ν (data u)

/-- For nonnegative viscosity the smaller producer reconstructs the previously
certified terminal producer, so no endpoint power is lost. -/
def actualNSToSignedGain_of_core
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (hν : 0 ≤ ν)
    (P : ActualNSToSignedGainCore State ActualNS ν data) :
    ActualNSToSignedGain State ActualNS ν data :=
  fun u hu => (P u hu).toCertificate hν

/-- Direct material bridge from a strict bulk/tail decomposition to the
minimal terminal signed-gain core.  No lower-order residual is needed: C=0.
Thus any genuine NS argument establishing two absorptive pieces with total
coefficient strictly below one immediately inhabits SignedGainCore. -/
def signedGainCoreOfBulkTail
    {ν : ℝ}
    {d : EnstrophyData}
    (bulk tail : ℝ → ℝ)
    (split : ∀ t, d.stretch t = bulk t + tail t)
    (cBulk δTail : ℝ)
    (hBulk0 : 0 ≤ cBulk)
    (hTail0 : 0 ≤ δTail)
    (hBulk : ∀ t, bulk t ≤ cBulk * ν * d.z t)
    (hTail : ∀ t, tail t ≤ δTail * ν * d.z t)
    (hBudget : cBulk + δTail < 1) :
    SignedGainCore ν d where
  theta := cBulk + δTail
  C := 0
  htheta1 := hBudget
  stretching := by
    intro t
    rw [split t]
    have hb := hBulk t
    have ht := hTail t
    nlinarith

/-- Nonempty form used by the producer-first terminal ledger. -/
theorem nonempty_signedGainCore_of_bulk_tail
    {ν : ℝ}
    {d : EnstrophyData}
    (bulk tail : ℝ → ℝ)
    (split : ∀ t, d.stretch t = bulk t + tail t)
    (cBulk δTail : ℝ)
    (hBulk0 : 0 ≤ cBulk)
    (hTail0 : 0 ≤ δTail)
    (hBulk : ∀ t, bulk t ≤ cBulk * ν * d.z t)
    (hTail : ∀ t, tail t ≤ δTail * ν * d.z t)
    (hBudget : cBulk + δTail < 1) :
    Nonempty (SignedGainCore ν d) :=
  ⟨signedGainCoreOfBulkTail bulk tail split cBulk δTail
    hBulk0 hTail0 hBulk hTail hBudget⟩

#print axioms NSProducerFirst.signedGainCoreOfBulkTail
#print axioms NSProducerFirst.nonempty_signedGainCore_of_bulk_tail

/-- Full terminal projection: a genuine NS-side bulk/tail construction for
every actual solution directly produces the current OPEN_MATH target. -/
def actualNSToSignedGainCore_of_bulkTail
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (bulk tail : State → ℝ → ℝ)
    (cBulk δTail : State → ℝ)
    (split :
      ∀ u, ActualNS u →
        ∀ t, (data u).stretch t = bulk u t + tail u t)
    (hBulk0 :
      ∀ u, ActualNS u → 0 ≤ cBulk u)
    (hTail0 :
      ∀ u, ActualNS u → 0 ≤ δTail u)
    (hBulk :
      ∀ u, ActualNS u →
        ∀ t, bulk u t ≤ cBulk u * ν * (data u).z t)
    (hTail :
      ∀ u, ActualNS u →
        ∀ t, tail u t ≤ δTail u * ν * (data u).z t)
    (hBudget :
      ∀ u, ActualNS u → cBulk u + δTail u < 1) :
    ActualNSToSignedGainCore State ActualNS ν data :=
  fun u hu =>
    signedGainCoreOfBulkTail
      (bulk u) (tail u) (split u hu)
      (cBulk u) (δTail u)
      (hBulk0 u hu) (hTail0 u hu)
      (hBulk u hu) (hTail u hu) (hBudget u hu)

#print axioms NSProducerFirst.actualNSToSignedGainCore_of_bulkTail

end NSProducerFirst
