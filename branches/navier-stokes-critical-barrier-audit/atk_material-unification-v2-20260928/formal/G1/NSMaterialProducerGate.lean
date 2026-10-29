import G1.HypothesesComplete_v2

namespace G1HypothesesV2

/-
Material audit:
conditional_G1_closure consumes DynamicCoherenceBridge and
KernelToDepletionBridge as supplied structures. Therefore it is a conditional
transport/composition theorem, not a material producer from ActualNS.
-/
theorem conditionalG1_is_transport
    (ActualNS : Prop)
    (ν : ℝ) (hν : 0 ≤ ν)
    (d : EnstrophyData)
    (hbal : EnstrophyBalance ν d)
    (dyn : DynamicCoherenceBridge ActualNS)
    (harm : KernelToDepletionBridge ν d)
    (hNS : ActualNS) :
    UniformEnstrophyDifferential ν d :=
  conditional_G1_closure ActualNS ν hν d hbal dyn harm hNS

#print axioms G1HypothesesV2.conditionalG1_is_transport

end G1HypothesesV2
