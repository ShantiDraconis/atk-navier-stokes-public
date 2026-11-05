/-!
Full fail-closed material-promotion architecture for the producer-first
Navier--Stokes lane.

Compile by concatenating after:
  ProducerFirst.lean
  SignedGainCore.lean
  NSMaterialInhabitant.lean
  ClayGlobalRegularityClosure.lean

This file does not inhabit the open PDE producer. It exposes, with exact
mathematical payloads, every downstream datum required for a legitimate
PROMOTED_BY_MATERIAL certificate.

The unique problem-specific OPEN_MATH input remains:
  ActualNSToSignedGainCore State ActualNS ν data.
-/

noncomputable section

namespace NSProducerFirst

def ExactEnstrophyBalance
    {State : Type}
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Prop :=
  ∀ u : State, ActualNS u →
    ∀ t : ℝ,
      (1 / 2 : ℝ) * deriv (data u).y t + ν * (data u).z t =
        (data u).stretch t

structure LerayEnergyRealization
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) where
  E0 : State → ℝ
  yMass : State → ℝ → ℝ
  hE0 : ∀ u, ActualNS u → 0 ≤ E0 u
  mass_spec :
    ∀ u, ActualNS u →
      ∀ T : ℝ,
        yMass u T = ∫ t in (0 : ℝ)..T, (data u).y t
  budget :
    ∀ u, ActualNS u →
      ∀ T : ℝ, 0 ≤ T →
        2 * ν * yMass u T ≤ E0 u

def UniformEnstrophyBound
    (d : EnstrophyData)
    (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → d.y t ≤ M

def gronwallMajorant
    (ν C E0 y0 : ℝ) : ℝ :=
  y0 * Real.exp (C * E0 / ν)

structure EnergyCompatibleGronwallBridge
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData)
    (energy : LerayEnergyRealization State ActualNS ν data) where
  close :
    ∀ u : State, ∀ hu : ActualNS u,
      ∀ theta C : ℝ,
        theta < 1 →
        0 ≤ C →
        (∀ t : ℝ,
          deriv (data u).y t +
              2 * (1 - theta) * ν * (data u).z t
            ≤ 2 * C * ((data u).y t)^2) →
        UniformEnstrophyBound
          (data u)
          (gronwallMajorant ν C (energy.E0 u) ((data u).y 0))

theorem material_to_uniform_enstrophy
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (hν : 0 < ν)
    (hMaterial : NSMaterialInhabitant State ActualNS ν data)
    (hBalance : ExactEnstrophyBalance ActualNS ν data)
    (energy : LerayEnergyRealization State ActualNS ν data)
    (gronwall :
      EnergyCompatibleGronwallBridge State ActualNS ν data energy) :
    ∀ u : State, ∀ hu : ActualNS u,
      let cert := materialInhabitant_certificate (le_of_lt hν) hMaterial u hu
      UniformEnstrophyBound
        (data u)
        (gronwallMajorant ν cert.C (energy.E0 u) ((data u).y 0)) := by
  intro u hu
  dsimp
  let cert :=
    materialInhabitant_certificate (le_of_lt hν) hMaterial u hu
  have hdiff :
      ∀ t : ℝ,
        deriv (data u).y t +
            2 * (1 - cert.theta) * ν * (data u).z t
          ≤ 2 * cert.C * ((data u).y t)^2 := by
    exact signedGain_implies_differential
      ν (data u) (hBalance u hu) cert
  exact gronwall.close u hu cert.theta cert.C
    cert.htheta1 cert.hC hdiff

structure EnstrophyToCriticalBridge
    (State : Type)
    (ActualNS : State → Prop)
    (data : State → EnstrophyData) where
  L3 : State → ℝ → ℝ
  hL3_nonneg :
    ∀ u, ActualNS u → ∀ t, 0 ≤ L3 u t
  criticalMajorant : State → ℝ → ℝ
  hmajorant_nonneg :
    ∀ u, ActualNS u → ∀ M, 0 ≤ M →
      0 ≤ criticalMajorant u M
  from_enstrophy :
    ∀ u, ActualNS u →
      ∀ M, UniformEnstrophyBound (data u) M →
        ∀ t : ℝ, 0 ≤ t →
          L3 u t ≤ criticalMajorant u M

structure CriticalContinuationBridge
    (State : Type)
    (ActualNS : State → Prop)
    (L3 : State → ℝ → ℝ)
    (GlobalRegularity : State → Prop) where
  continuation_rule :
    ∀ u : State, ActualNS u →
      ∀ M : ℝ, 0 ≤ M →
        (∀ t : ℝ, 0 ≤ t → L3 u t ≤ M) →
        GlobalRegularity u

structure MaterialDownstreamPackage
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData)
    (GlobalRegularity : State → Prop) where
  hν : 0 < ν
  balance : ExactEnstrophyBalance ActualNS ν data
  energy : LerayEnergyRealization State ActualNS ν data
  gronwall :
    EnergyCompatibleGronwallBridge State ActualNS ν data energy
  critical :
    EnstrophyToCriticalBridge State ActualNS data
  continuation :
    CriticalContinuationBridge
      State ActualNS critical.L3 GlobalRegularity

structure PromotedByMaterial
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData)
    (GlobalRegularity : State → Prop) where
  material : NSMaterialInhabitant State ActualNS ν data
  downstream :
    MaterialDownstreamPackage State ActualNS ν data GlobalRegularity

theorem promotedByMaterial_global
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    {GlobalRegularity : State → Prop}
    (cert :
      PromotedByMaterial State ActualNS ν data GlobalRegularity) :
    ∀ u : State, ActualNS u → GlobalRegularity u := by
  intro u hu
  let sg :=
    materialInhabitant_certificate
      (le_of_lt cert.downstream.hν)
      cert.material u hu
  have hE :
      UniformEnstrophyBound
        (data u)
        (gronwallMajorant
          ν sg.C (cert.downstream.energy.E0 u) ((data u).y 0)) := by
    exact material_to_uniform_enstrophy
      cert.downstream.hν
      cert.material
      cert.downstream.balance
      cert.downstream.energy
      cert.downstream.gronwall
      u hu
  let M :=
    gronwallMajorant
      ν sg.C (cert.downstream.energy.E0 u) ((data u).y 0)
  let K := cert.downstream.critical.criticalMajorant u M
  have hM : 0 ≤ M := hE.1
  have hK : 0 ≤ K :=
    cert.downstream.critical.hmajorant_nonneg u hu M hM
  have hcrit : ∀ t : ℝ, 0 ≤ t →
      cert.downstream.critical.L3 u t ≤ K := by
    intro t ht
    exact cert.downstream.critical.from_enstrophy
      u hu M hE t ht
  exact cert.downstream.continuation.continuation_rule u hu K hK hcrit

theorem promotedByMaterial_proves_ClayA
    (I : ClayAInterface)
    (ν : ℝ)
    (data : I.State → EnstrophyData)
    (GlobalRegularity : I.State → Prop)
    (cert :
      PromotedByMaterial
        I.State I.ActualNS ν data GlobalRegularity) :
    ClayAStatement I GlobalRegularity := by
  intro u0 hu0
  have hNS : I.ActualNS (I.solution u0) :=
    I.actual_solution u0 hu0
  exact promotedByMaterial_global cert (I.solution u0) hNS

theorem promotedByMaterial_requires_material
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    {GlobalRegularity : State → Prop} :
    Nonempty
      (PromotedByMaterial State ActualNS ν data GlobalRegularity) →
    Nonempty
      (NSMaterialInhabitant State ActualNS ν data) := by
  rintro ⟨cert⟩
  exact ⟨cert.material⟩

end NSProducerFirst
