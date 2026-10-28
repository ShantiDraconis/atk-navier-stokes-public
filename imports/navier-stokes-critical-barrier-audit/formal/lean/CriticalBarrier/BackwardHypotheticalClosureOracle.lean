import CriticalBarrier.GlobalRegularityFromG1

namespace CriticalBarrier.BackwardAudit

variable {State : Type}

def HypotheticalClosure
    (ActualNS GlobalRegularity : State → Prop) : Prop :=
  ∀ u, ActualNS u → GlobalRegularity u

theorem hypothetical_global_regularity
    {ActualNS GlobalRegularity : State → Prop}
    (H : HypotheticalClosure ActualNS GlobalRegularity)
    (u : State) (hu : ActualNS u) :
    GlobalRegularity u :=
  H u hu

#print axioms CriticalBarrier.BackwardAudit.hypothetical_global_regularity

end CriticalBarrier.BackwardAudit
