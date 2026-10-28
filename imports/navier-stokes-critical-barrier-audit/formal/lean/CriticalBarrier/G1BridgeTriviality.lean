import CriticalBarrier.GlobalRegularityFromG1

namespace CriticalBarrier.G1BridgeTriviality

open CriticalBarrier.GlobalRegularityFromG1

variable {State : Type}

/-- Counter-audit: the current abstract G1Bridge does not tie its stretching
data to the supplied state. Therefore it is inhabited for every ActualNS
predicate by choosing identically-zero analytic data. -/
noncomputable def trivialG1Bridge
    (ActualNS : State → Prop) : G1Bridge ActualNS where
  defect := fun _ _ => 0
  stretchingData := fun _ _ =>
    { y := 0
      z := 0
      stretching := 0
      nu := 1
      theta := 0
      a := 0
      y_nonneg := by norm_num
      z_nonneg := by norm_num
      nu_pos := by norm_num
      theta_nonneg := by norm_num
      theta_lt_one := by norm_num }
  actual_to_signed := by
    intro u hu t
    simp [SignedDepletionAt]
  defect_integrable := by
    intro u hu
    simp

theorem g1Bridge_inhabited_for_every_ActualNS
    (ActualNS : State → Prop) :
    Nonempty (G1Bridge ActualNS) :=
  ⟨trivialG1Bridge ActualNS⟩

end CriticalBarrier.G1BridgeTriviality
