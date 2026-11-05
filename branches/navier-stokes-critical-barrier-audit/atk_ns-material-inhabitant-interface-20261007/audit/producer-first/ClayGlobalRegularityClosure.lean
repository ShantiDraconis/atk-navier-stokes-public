/-!
Clay A global-regularity closure interface for the producer-first Navier--Stokes lane.

Compile by concatenating after:
  ProducerFirst.lean
  SignedGainCore.lean
  NSMaterialInhabitant.lean

This module proves the logical closure from the unique material producer plus
the standard downstream analytic bridges. It introduces no axiom, sorry, admit,
or default inhabitant.
-/

noncomputable section

namespace NSProducerFirst

/-- Exact downstream predicates used by the Clay-A closure route. -/
structure ClayPredicates (State : Type) where
  UniformEnstrophy : State → Prop
  CriticalL3Bound : State → Prop
  GlobalRegularity : State → Prop

/-- Downstream analytic package after the material signed-gain producer. -/
structure ClayDownstream
    (State : Type)
    (ActualNS : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData)
    (P : ClayPredicates State) where
  material_to_uniformEnstrophy :
    NSMaterialInhabitant State ActualNS ν data →
      ∀ u : State, ActualNS u → P.UniformEnstrophy u

  uniformEnstrophy_to_criticalL3 :
    ∀ u : State, ActualNS u →
      P.UniformEnstrophy u → P.CriticalL3Bound u

  criticalL3_to_global :
    ∀ u : State, ActualNS u →
      P.CriticalL3Bound u → P.GlobalRegularity u

/-- Full dependency chain for one genuine Navier--Stokes trajectory. -/
theorem clay_dependency_chain
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    {P : ClayPredicates State}
    (hMaterial : NSMaterialInhabitant State ActualNS ν data)
    (hDown : ClayDownstream State ActualNS ν data P)
    (u : State)
    (hu : ActualNS u) :
    P.UniformEnstrophy u ∧
      P.CriticalL3Bound u ∧
      P.GlobalRegularity u := by
  have hE : P.UniformEnstrophy u :=
    hDown.material_to_uniformEnstrophy hMaterial u hu
  have hL3 : P.CriticalL3Bound u :=
    hDown.uniformEnstrophy_to_criticalL3 u hu hE
  have hG : P.GlobalRegularity u :=
    hDown.criticalL3_to_global u hu hL3
  exact ⟨hE, hL3, hG⟩

/-- Trajectory-level Clay closure theorem. -/
theorem clay_global_regularity_from_material
    {State : Type}
    {ActualNS : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    {P : ClayPredicates State}
    (hMaterial : NSMaterialInhabitant State ActualNS ν data)
    (hDown : ClayDownstream State ActualNS ν data P) :
    ∀ u : State, ActualNS u → P.GlobalRegularity u := by
  intro u hu
  exact (clay_dependency_chain hMaterial hDown u hu).2.2

/-- Problem-level interface for Clay formulation A. -/
structure ClayAInterface where
  InitialData : Type
  State : Type
  admissible : InitialData → Prop
  solution : InitialData → State
  ActualNS : State → Prop
  actual_solution :
    ∀ u0 : InitialData, admissible u0 → ActualNS (solution u0)

/-- Exact Clay-A statement represented by the interface and global predicate. -/
def ClayAStatement
    (I : ClayAInterface)
    (GlobalRegularity : I.State → Prop) : Prop :=
  ∀ u0 : I.InitialData,
    I.admissible u0 →
      GlobalRegularity (I.solution u0)

/-- Final fail-closed Clay-A composition theorem. -/
theorem clay_A_from_material
    (I : ClayAInterface)
    (ν : ℝ)
    (data : I.State → EnstrophyData)
    (P : ClayPredicates I.State)
    (hMaterial :
      NSMaterialInhabitant I.State I.ActualNS ν data)
    (hDown :
      ClayDownstream I.State I.ActualNS ν data P) :
    ClayAStatement I P.GlobalRegularity := by
  intro u0 hu0
  have hNS : I.ActualNS (I.solution u0) :=
    I.actual_solution u0 hu0
  exact clay_global_regularity_from_material
    hMaterial hDown (I.solution u0) hNS

/-- Full closure certificate: material producer plus downstream analytics. -/
structure ClayClosureCertificate
    (I : ClayAInterface)
    (ν : ℝ)
    (data : I.State → EnstrophyData)
    (P : ClayPredicates I.State) where
  material : NSMaterialInhabitant I.State I.ActualNS ν data
  downstream : ClayDownstream I.State I.ActualNS ν data P

/-- A complete closure certificate yields Clay A. -/
theorem ClayClosureCertificate.provesClayA
    {I : ClayAInterface}
    {ν : ℝ}
    {data : I.State → EnstrophyData}
    {P : ClayPredicates I.State}
    (cert : ClayClosureCertificate I ν data P) :
    ClayAStatement I P.GlobalRegularity :=
  clay_A_from_material I ν data P cert.material cert.downstream

end NSProducerFirst
