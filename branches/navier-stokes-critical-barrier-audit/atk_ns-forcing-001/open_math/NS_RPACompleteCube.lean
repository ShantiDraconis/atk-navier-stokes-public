import open_math.RPA_EndpointLattice
import open_math.NS_MaterialPrizeGate

/-!
Navier--Stokes-specific instantiation of the complete RPA cube.

This file certifies the structural 14-node cube + FULL for NS labels.
It does not construct the unresolved material NS payload.
-/

namespace NSRPACube

open RPA.EndpointLattice
open NSMaterialPrizeGate
open NSProducerFirst

abbrev OPEN_NS : FreeState := openFree
abbrev CLOSED_NS : FreeState := closedFree

abbrev DUAL_NS : FreeState := OPEN_NS + CLOSED_NS

abbrev OPEN_OPEN_NS : FreeState :=
  OPEN_NS + OPEN_NS

abbrev CLOSED_CLOSED_NS : FreeState :=
  CLOSED_NS + CLOSED_NS

abbrev OPEN_OPEN_OPEN_NS : FreeState :=
  OPEN_NS + OPEN_NS + OPEN_NS

abbrev CLOSED_CLOSED_CLOSED_NS : FreeState :=
  CLOSED_NS + CLOSED_NS + CLOSED_NS

abbrev OPEN_OPEN_CLOSED_NS : FreeState :=
  OPEN_NS + OPEN_NS + CLOSED_NS

abbrev OPEN_CLOSED_OPEN_NS : FreeState :=
  OPEN_NS + CLOSED_NS + OPEN_NS

abbrev CLOSED_OPEN_OPEN_NS : FreeState :=
  CLOSED_NS + OPEN_NS + OPEN_NS

abbrev OPEN_CLOSED_CLOSED_NS : FreeState :=
  OPEN_NS + CLOSED_NS + CLOSED_NS

abbrev CLOSED_OPEN_CLOSED_NS : FreeState :=
  CLOSED_NS + OPEN_NS + CLOSED_NS

abbrev CLOSED_CLOSED_OPEN_NS : FreeState :=
  CLOSED_NS + CLOSED_NS + OPEN_NS

abbrev FULL_NS_FREE : FreeState :=
  OPEN_NS + OPEN_NS + CLOSED_NS + CLOSED_NS

@[simp] theorem dual_ns_canonical :
    canonicalize DUAL_NS = .full := rfl

@[simp] theorem open_open_ns_canonical :
    canonicalize OPEN_OPEN_NS = .openOnly := rfl

@[simp] theorem closed_closed_ns_canonical :
    canonicalize CLOSED_CLOSED_NS = .closedOnly := rfl

@[simp] theorem open_open_open_ns_canonical :
    canonicalize OPEN_OPEN_OPEN_NS = .openOnly := rfl

@[simp] theorem closed_closed_closed_ns_canonical :
    canonicalize CLOSED_CLOSED_CLOSED_NS = .closedOnly := rfl

@[simp] theorem open_open_closed_ns_canonical :
    canonicalize OPEN_OPEN_CLOSED_NS = .full := rfl

@[simp] theorem open_closed_open_ns_canonical :
    canonicalize OPEN_CLOSED_OPEN_NS = .full := rfl

@[simp] theorem closed_open_open_ns_canonical :
    canonicalize CLOSED_OPEN_OPEN_NS = .full := rfl

@[simp] theorem open_closed_closed_ns_canonical :
    canonicalize OPEN_CLOSED_CLOSED_NS = .full := rfl

@[simp] theorem closed_open_closed_ns_canonical :
    canonicalize CLOSED_OPEN_CLOSED_NS = .full := rfl

@[simp] theorem closed_closed_open_ns_canonical :
    canonicalize CLOSED_CLOSED_OPEN_NS = .full := rfl

@[simp] theorem full_ns_free_canonical :
    canonicalize FULL_NS_FREE = .full := rfl

/-- The structural FULL view for NS. This is definitional RPA content only. -/
def FULL_NS (Open Closed : Prop) : Prop :=
  RPA.EndpointLattice.FULL Open Closed

/-- A material global certificate requires BOTH structural FULL and the
problem-specific analytic NS closure payload. -/
structure NSGlobalCertificate
    (State : Type)
    (ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop)
    (ν : ℝ)
    (data : State → EnstrophyData)
    (Open Closed : Prop) where
  full : FULL_NS Open Closed
  material :
    NSFinalClosureMaterial State ActualNS SmoothGlobal NoBlowup
      EnergyControlled CriticalRegular ν data

/-- Structural FULL alone cannot be promoted by this constructor; the material
payload is an explicit required argument. -/
def ns_global_certificate
    {State : Type}
    {ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop}
    {ν : ℝ}
    {data : State → EnstrophyData}
    {Open Closed : Prop}
    (hFull : FULL_NS Open Closed)
    (hMaterial :
      NSFinalClosureMaterial State ActualNS SmoothGlobal NoBlowup
        EnergyControlled CriticalRegular ν data) :
    NSGlobalCertificate State ActualNS SmoothGlobal NoBlowup
      EnergyControlled CriticalRegular ν data Open Closed :=
  ⟨hFull, hMaterial⟩

end NSRPACube
