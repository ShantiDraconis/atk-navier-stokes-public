import CriticalBarrier.GlobalRegularityFromG1

namespace CriticalBarrier.OpenMath

open CriticalBarrier.GlobalRegularityFromG1

def FirstRealOpenMath
    {State : Type}
    (ActualNS : State → Prop) : Prop :=
  Nonempty (G1Bridge ActualNS)

theorem expose_G1
    {State : Type}
    {ActualNS : State → Prop}
    (h : FirstRealOpenMath ActualNS) :
    Nonempty (G1Bridge ActualNS) := h

#print axioms CriticalBarrier.OpenMath.expose_G1

end CriticalBarrier.OpenMath
