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

end NSProducerFirst
