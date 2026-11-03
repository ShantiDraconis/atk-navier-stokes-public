import open_math.RPA_EndpointLattice
import open_math.NS_MaterialPrizeGate

/-!
Navier--Stokes endpoint cube.

This instantiates the generic RPA lattice for the NS lane.  The 14 finite
states plus FULL are structural.  A final NS certificate additionally requires
the material NS payload; the lattice alone cannot produce it.
-/

namespace NSMaterialPrizeGate.NSCube

open RPA.EndpointLattice

/-- NS endpoint positions in the canonical idempotent quotient. -/
def OPEN_NS : Canonical := .openOnly
def CLOSED_NS : Canonical := .closedOnly

theorem open_ns_ne_closed_ns : OPEN_NS ≠ CLOSED_NS := by
  decide

/-- Base dual structural state. -/
def DUAL_NS : Canonical := join OPEN_NS CLOSED_NS

@[simp] theorem dual_ns_eq_full :
    DUAL_NS = .full := rfl

/-- Two-state words. -/
def OPEN_CLOSED_NS : FreeState := openFree + closedFree
def CLOSED_OPEN_NS : FreeState := closedFree + openFree
def OPEN_OPEN_NS : FreeState := openFree + openFree
def CLOSED_CLOSED_NS : FreeState := closedFree + closedFree

@[simp] theorem open_closed_ns_canonical :
    canonicalize OPEN_CLOSED_NS = .full := rfl
@[simp] theorem closed_open_ns_canonical :
    canonicalize CLOSED_OPEN_NS = .full := rfl
@[simp] theorem open_open_ns_canonical :
    canonicalize OPEN_OPEN_NS = .openOnly := rfl
@[simp] theorem closed_closed_ns_canonical :
    canonicalize CLOSED_CLOSED_NS = .closedOnly := rfl

/-- Three-state words. -/
def OPEN_OPEN_OPEN_NS : FreeState :=
  openFree + openFree + openFree
def CLOSED_CLOSED_CLOSED_NS : FreeState :=
  closedFree + closedFree + closedFree

def OPEN_OPEN_CLOSED_NS : FreeState :=
  openFree + openFree + closedFree
def OPEN_CLOSED_OPEN_NS : FreeState :=
  openFree + closedFree + openFree
def CLOSED_OPEN_OPEN_NS : FreeState :=
  closedFree + openFree + openFree

def OPEN_CLOSED_CLOSED_NS : FreeState :=
  openFree + closedFree + closedFree
def CLOSED_OPEN_CLOSED_NS : FreeState :=
  closedFree + openFree + closedFree
def CLOSED_CLOSED_OPEN_NS : FreeState :=
  closedFree + closedFree + openFree

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

/-- FULL structural NS state = two OPEN + two CLOSED. -/
def FULL_NS : FreeState :=
  openFree + openFree + closedFree + closedFree

@[simp] theorem full_ns_counts :
    FULL_NS = ⟨2, 2⟩ := rfl

@[simp] theorem full_ns_canonical :
    canonicalize FULL_NS = .full := rfl

/-- All 14 requested NS nodes plus FULL are present structurally. -/
theorem ns_cube_complete :
    canonicalize openFree = .openOnly ∧
    canonicalize closedFree = .closedOnly ∧
    canonicalize OPEN_CLOSED_NS = .full ∧
    canonicalize CLOSED_OPEN_NS = .full ∧
    canonicalize OPEN_OPEN_NS = .openOnly ∧
    canonicalize CLOSED_CLOSED_NS = .closedOnly ∧
    canonicalize OPEN_OPEN_OPEN_NS = .openOnly ∧
    canonicalize CLOSED_CLOSED_CLOSED_NS = .closedOnly ∧
    canonicalize OPEN_OPEN_CLOSED_NS = .full ∧
    canonicalize OPEN_CLOSED_OPEN_NS = .full ∧
    canonicalize CLOSED_OPEN_OPEN_NS = .full ∧
    canonicalize OPEN_CLOSED_CLOSED_NS = .full ∧
    canonicalize CLOSED_OPEN_CLOSED_NS = .full ∧
    canonicalize CLOSED_CLOSED_OPEN_NS = .full ∧
    canonicalize FULL_NS = .full := by
  repeat' apply And.intro
  all_goals rfl

/-- Final NS certificate object: structural FULL plus the independent material
closure.  This cannot be inhabited from the lattice alone. -/
structure NSGlobalCertificate
    (State : Type)
    (ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop)
    (ν : ℝ)
    (data : State → NSProducerFirst.EnstrophyData) where
  fullStructural : canonicalize FULL_NS = .full
  material :
    NSFinalClosureMaterial State ActualNS SmoothGlobal NoBlowup
      EnergyControlled CriticalRegular ν data

/-- Once the material payload exists, the already-closed structural FULL node
packages with it into the global NS certificate. -/
def ns_global_certificate_of_material
    {State : Type}
    {ActualNS SmoothGlobal NoBlowup EnergyControlled CriticalRegular : State → Prop}
    {ν : ℝ}
    {data : State → NSProducerFirst.EnstrophyData}
    (hMaterial :
      NSFinalClosureMaterial State ActualNS SmoothGlobal NoBlowup
        EnergyControlled CriticalRegular ν data) :
    NSGlobalCertificate State ActualNS SmoothGlobal NoBlowup
      EnergyControlled CriticalRegular ν data where
  fullStructural := full_ns_canonical
  material := hMaterial

end NSMaterialPrizeGate.NSCube
