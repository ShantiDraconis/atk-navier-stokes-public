import open_math.NS_ProducerFirstAPI
import open_math.RPA_MinimalChain
import open_math.RPA_EndpointLattice

/-!
Navier--Stokes material prize-gate schema.

This file does not assert a Millennium solution.  It exposes the three gates
that must all be inhabited before any material closure can be promoted.
-/

noncomputable section

namespace NSMaterialPrizeGate

open NSProducerFirst

/-- Gate 1: existence of an actual NS state in the chosen carrier. -/
def NSExistenceGate
    (State : Type)
    (ActualNS : State → Prop) : Prop :=
  ∃ u : State, ActualNS u

/-- Gate 2: a problem-specific smoothness/regularity predicate holds for every
actual NS state.  The predicate is left explicit rather than smuggled into the
carrier. -/
def NSSmoothnessGate
    (State : Type)
    (ActualNS SmoothGlobal : State → Prop) : Prop :=
  ∀ u : State, ActualNS u → SmoothGlobal u

/-- Material PDE payload.  The decisive field is the actual signed-gain
producer; the other fields are downstream semantic consequences supplied
explicitly by the caller. -/
structure NSMaterialPayload
    (State : Type)
    (ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) where
  signedGain :
    ActualNSToSignedGain State ActualNS ν data
  noBlowup :
    ∀ u, ActualNS u → NoBlowup u
  energy :
    ∀ u, ActualNS u → EnergyControlled u
  criticalRegularity :
    ∀ u, ActualNS u → CriticalRegular u
  smooth :
    ∀ u, ActualNS u → SmoothGlobal u

/-- Gate 3: final material closure is exactly nonemptiness of the analytic
payload; structural RPA/FULL data alone cannot inhabit it. -/
def NSFinalClosureMaterial
    (State : Type)
    (ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Prop :=
  Nonempty
    (NSMaterialPayload State ActualNS SmoothGlobal NoBlowup
      EnergyControlled CriticalRegular ν data)

/-- The complete prize gate requires all three material gates simultaneously. -/
def NSPrizeTripleGate
    (State : Type)
    (ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData) : Prop :=
  NSExistenceGate State ActualNS ∧
  NSSmoothnessGate State ActualNS SmoothGlobal ∧
  NSFinalClosureMaterial State ActualNS SmoothGlobal NoBlowup
    EnergyControlled CriticalRegular ν data

/-- Material closure implies the smoothness gate, but not conversely. -/
theorem finalClosure_implies_smoothness
    {State : Type}
    {ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    (h : NSFinalClosureMaterial State ActualNS SmoothGlobal NoBlowup
      EnergyControlled CriticalRegular ν data) :
    NSSmoothnessGate State ActualNS SmoothGlobal := by
  rcases h with ⟨P⟩
  exact P.smooth

/-- Structural FULL/RPA is intentionally not accepted as a substitute for the
material analytic payload.  A caller must provide the payload separately. -/
theorem structural_full_plus_material_closes
    {State : Type}
    {ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    {Open Closed : Prop}
    (_hFull : RPA.EndpointLattice.FULL Open Closed)
    (hMaterial : NSFinalClosureMaterial State ActualNS SmoothGlobal NoBlowup
      EnergyControlled CriticalRegular ν data) :
    NSFinalClosureMaterial State ActualNS SmoothGlobal NoBlowup
      EnergyControlled CriticalRegular ν data :=
  hMaterial

end NSMaterialPrizeGate
