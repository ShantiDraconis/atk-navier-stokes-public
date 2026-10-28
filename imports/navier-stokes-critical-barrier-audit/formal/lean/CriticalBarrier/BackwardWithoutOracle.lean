import CriticalBarrier.GlobalRegularityFromG1

namespace CriticalBarrier.BackwardAudit

open CriticalBarrier.GlobalRegularityFromG1

variable {State : Type}

structure IndependentClosureContract
    (ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity : State → Prop) where
  g1 : G1Bridge ActualNS
  downstream :
    DownstreamClosure ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity

theorem independent_contract_closes
    {ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity : State → Prop}
    (C : IndependentClosureContract
      ActualNS UniformEnstrophy CriticalL3Bound GlobalRegularity) :
    ∀ u, ActualNS u → GlobalRegularity u :=
  global_regularity_from_G1 C.g1 C.downstream

/-- The repository does not claim construction of the independent contract
    from bare ActualNS dynamics. -/
def actualNSProducesClosureContract : Bool := false

theorem actualNS_to_contract_still_open :
    actualNSProducesClosureContract = false := by rfl

#print axioms CriticalBarrier.BackwardAudit.independent_contract_closes
#print axioms CriticalBarrier.BackwardAudit.actualNS_to_contract_still_open

end CriticalBarrier.BackwardAudit
