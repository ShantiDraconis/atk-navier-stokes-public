/-!
Concrete Navier--Stokes material terminal adapter.

This file is intended to be kernel-checked by concatenating it after
audit/producer-first/ProducerFirst.lean and
audit/producer-first/SignedGainCore.lean, matching the repository's existing
producer-first workflow.

No axiom and no sorry is introduced here.

Important boundary:
* NavierStokesMaterialCertifies is the exact current PDE producer
  ActualNSToSignedGainCore.
* This file does NOT identify that producer with unconditional global
  regularity, because the repository still lacks a theorem connecting this
  producer to the independent G1/downstream global-regularity contract without
  additional mathematical input.
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

theorem bulkTail_certifies_navierStokesMaterial
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
    NavierStokesMaterialCertifies State ActualNS ν data := by
  refine ⟨?_⟩
  exact actualNSToSignedGainCore_of_bulkTail
    bulk tail cBulk δTail split hBulk0 hTail0 hBulk hTail hBudget



/-- Core-to-differential compression. Once the exact enstrophy balance is
available, the minimal signed-gain core yields the differential inequality
without reopening the bulk/tail decomposition. -/
theorem signedGainCore_implies_differential
    {ν : ℝ} {d : EnstrophyData}
    (hν : 0 ≤ ν)
    (hbalance : ∀ t,
      (1 / 2 : ℝ) * deriv d.y t + ν * d.z t = d.stretch t)
    (h : SignedGainCore ν d) :
    ∀ t,
      deriv d.y t + 2 * (1 - max h.theta 0) * ν * d.z t
        ≤ 2 * max h.C 0 * (d.y t)^2 := by
  exact signedGain_implies_differential
    ν d hbalance (h.toCertificate hν)

/-- Universalized forward map: a material producer for every actual solution,
plus the exact enstrophy balance, yields the same differential inequality for
every actual solution. No Gronwall or endpoint theorem is assumed here. -/
theorem actualNSCore_implies_differential
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (hν : 0 ≤ ν)
    (P : ActualNSToSignedGainCore State ActualNS ν data)
    (hbalance : ∀ u, ActualNS u →
      ∀ t, (1 / 2 : ℝ) * deriv (data u).y t +
        ν * (data u).z t = (data u).stretch t) :
    ∀ u, ∀ hu : ActualNS u, ∀ t,
        deriv (data u).y t +
            2 * (1 - max (P u hu).theta 0) * ν * (data u).z t
          ≤ 2 * max (P u hu).C 0 * ((data u).y t)^2 := by
  intro u hu
  exact signedGainCore_implies_differential
    hν (hbalance u hu) (P u hu)

/-- The remaining analytic coefficient after the signed-gain reduction. -/
def signedGainCoreCoefficient
    {ν : ℝ} {d : EnstrophyData}
    (h : SignedGainCore ν d) (t : ℝ) : ℝ :=
  max h.C 0 * d.y t

theorem signedGainCoreCoefficient_nonnegative
    {ν : ℝ} {d : EnstrophyData}
    (h : SignedGainCore ν d) :
    ∀ t, 0 ≤ signedGainCoreCoefficient h t := by
  intro t
  exact mul_nonneg (le_max_right _ _) (d.hy t)

/-- Exact residual identity: the post-G1 nonlinear remainder is a(t)*y(t)
with a(t)=max(C,0)*y(t). This isolates the next analytic obligation as time
control of a, rather than another geometric stretching estimate. -/
theorem signedGainCore_residual_factorization
    {ν : ℝ} {d : EnstrophyData}
    (h : SignedGainCore ν d) :
    ∀ t,
      signedGainCoreCoefficient h t * d.y t =
        max h.C 0 * (d.y t)^2 := by
  intro t
  simp [signedGainCoreCoefficient, pow_two, mul_assoc]



/-- No new analytic estimate is needed to control the *form* of the residual:
if enstrophy is L1 in time, then the exact coefficient a(t)=max(C,0)*y(t)
is L1 in time as well. -/
theorem signedGainCoreCoefficient_integrableOn_nonnegativeTime
    {ν : ℝ} {d : EnstrophyData}
    (h : SignedGainCore ν d)
    (hy : IntegrableOn d.y (Set.Ici (0 : ℝ))) :
    IntegrableOn (signedGainCoreCoefficient h) (Set.Ici (0 : ℝ)) := by
  simpa [signedGainCoreCoefficient] using
    hy.const_mul (max h.C 0)

/-- Exact next producer after signed gain: the actual NS dynamics must supply
time-integrability of enstrophy on the physical half-line t >= 0. -/
def ActualNSToEnstrophyL1
    (State : Type)
    (ActualNS : State → Prop)
    (data : State → EnstrophyData) : Prop :=
  ∀ u, ActualNS u → IntegrableOn (data u).y (Set.Ici (0 : ℝ))

/-- Once the actual NS class supplies L1 enstrophy on nonnegative time, every
material signed-gain core has an L1 residual coefficient on the same domain. -/
theorem actualNSCore_coefficient_integrableOn_nonnegativeTime
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (P : ActualNSToSignedGainCore State ActualNS ν data)
    (hL1 : ActualNSToEnstrophyL1 State ActualNS data) :
    ∀ u, ∀ hu : ActualNS u,
      IntegrableOn
        (signedGainCoreCoefficient (P u hu))
        (Set.Ici (0 : ℝ)) := by
  intro u hu
  exact signedGainCoreCoefficient_integrableOn_nonnegativeTime
    (P u hu) (hL1 u hu)

def NavierStokesMaterialOpenMath
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Prop :=
  NavierStokesMaterialCertifies State ActualNS ν data

#print axioms NSProducerFirst.not_navierStokesMaterialCertifies_iff_refutes
#print axioms NSProducerFirst.navierStokes_material_cert_refute_disjoint
#print axioms NSProducerFirst.bulkTail_certifies_navierStokesMaterial
#print axioms NSProducerFirst.signedGainCore_implies_differential
#print axioms NSProducerFirst.actualNSCore_implies_differential
#print axioms NSProducerFirst.signedGainCore_residual_factorization
#print axioms NSProducerFirst.signedGainCoreCoefficient_integrableOn_nonnegativeTime
#print axioms NSProducerFirst.actualNSCore_coefficient_integrableOn_nonnegativeTime

end NSProducerFirst
