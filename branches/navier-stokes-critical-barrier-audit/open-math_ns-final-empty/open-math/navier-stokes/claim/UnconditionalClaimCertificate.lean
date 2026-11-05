import CriticalBarrier.OpenMath.NavierStokes.OpenMathCore
import CriticalBarrier.GlobalRegularityFromG1

namespace NSUnconditionalClaimCertificate

open CriticalBarrier.OpenMath.NavierStokes
open CriticalBarrier.GlobalRegularityFromG1

variable {State : Type}

structure TerminalAdapter
    (ActualNS GlobalRegularity : State → Prop) where
  FinalTheorem : Prop
  export :
    (∀ u, ActualNS u → GlobalRegularity u) → FinalTheorem

structure Certificate
    (ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity : State → Prop)
    (D : PhysicalStretchingData (State := State))
    (T : TerminalAdapter ActualNS GlobalRegularity) where
  core : NSOpenMathCore ActualNS D
  downstream :
    DownstreamClosure ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity

theorem certificate_enables_final_theorem
    (ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity : State → Prop)
    (D : PhysicalStretchingData (State := State))
    (T : TerminalAdapter ActualNS GlobalRegularity)
    (C : Certificate ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity D T) :
    T.FinalTheorem := by
  rcases C.core with ⟨P⟩
  have hG1 : G1Bridge ActualNS := P.toG1Bridge
  have hReg : ∀ u, ActualNS u → GlobalRegularity u :=
    global_regularity_from_G1
      ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity
      hG1 C.downstream
  exact T.export hReg

theorem certificate_requires_open_math_core
    (ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity : State → Prop)
    (D : PhysicalStretchingData (State := State))
    (T : TerminalAdapter ActualNS GlobalRegularity)
    (C : Certificate ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity D T) :
    NSOpenMathCore ActualNS D :=
  C.core

def create
    (ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity : State → Prop)
    (D : PhysicalStretchingData (State := State))
    (T : TerminalAdapter ActualNS GlobalRegularity)
    (hCore : NSOpenMathCore ActualNS D)
    (hDown :
      DownstreamClosure ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity) :
    Certificate ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity D T where
  core := hCore
  downstream := hDown

#print axioms certificate_enables_final_theorem
#print axioms certificate_requires_open_math_core
#print axioms create

end NSUnconditionalClaimCertificate
