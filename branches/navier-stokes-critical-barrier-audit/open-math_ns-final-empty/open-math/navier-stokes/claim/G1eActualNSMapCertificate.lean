import CriticalBarrier.OpenMath.NavierStokes.OpenMathCore

namespace NSG1eActualNSMapCertificate

open CriticalBarrier.OpenMath.NavierStokes

variable {State : Type}

/-- Exact prize-deciding producer.

This is deliberately not a metadata certificate and not a renamed regularity
assumption.  Its payload is the physical strict signed-depletion producer that
must be derived from actual 3D incompressible Navier-Stokes dynamics. -/
structure G1eActualNSMap
    (ActualNS : State → Prop)
    (D : PhysicalStretchingData (State := State)) where
  produce : StrictSignedDepletionProducer ActualNS D

def G1eClosed
    (ActualNS : State → Prop)
    (D : PhysicalStretchingData (State := State)) : Prop :=
  Nonempty (G1eActualNSMap ActualNS D)

/-- G1e is exactly strong enough to close the canonical OPEN_MATH core. -/
theorem g1e_implies_open_math_core
    (ActualNS : State → Prop)
    (D : PhysicalStretchingData (State := State))
    (h : G1eClosed ActualNS D) :
    NSOpenMathCore ActualNS D := by
  rcases h with ⟨g⟩
  exact ⟨g.produce⟩

/-- Conversely, any genuine inhabitant of the canonical core is already a
G1e certificate.  Therefore G1e introduces no extra hidden obligation. -/
theorem open_math_core_implies_g1e
    (ActualNS : State → Prop)
    (D : PhysicalStretchingData (State := State))
    (h : NSOpenMathCore ActualNS D) :
    G1eClosed ActualNS D := by
  rcases h with ⟨p⟩
  exact ⟨⟨p⟩⟩

theorem g1e_iff_open_math_core
    (ActualNS : State → Prop)
    (D : PhysicalStretchingData (State := State)) :
    G1eClosed ActualNS D ↔ NSOpenMathCore ActualNS D :=
  ⟨g1e_implies_open_math_core ActualNS D,
   open_math_core_implies_g1e ActualNS D⟩

#print axioms g1e_implies_open_math_core
#print axioms open_math_core_implies_g1e
#print axioms g1e_iff_open_math_core

end NSG1eActualNSMapCertificate
