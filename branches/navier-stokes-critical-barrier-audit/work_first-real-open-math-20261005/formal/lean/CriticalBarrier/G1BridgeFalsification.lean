import CriticalBarrier.GlobalRegularityFromG1

namespace CriticalBarrier.GlobalRegularityFromG1

noncomputable def trivialG1Bridge
    {State : Type}
    (ActualNS : State → Prop) :
    G1Bridge ActualNS where
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
    simpa using (MeasureTheory.integrable_zero : MeasureTheory.Integrable (fun _ : ℝ => (0 : ℝ)))

theorem g1Bridge_is_trivially_inhabited
    {State : Type}
    (ActualNS : State → Prop) :
    Nonempty (G1Bridge ActualNS) :=
  ⟨trivialG1Bridge ActualNS⟩

#print axioms CriticalBarrier.GlobalRegularityFromG1.g1Bridge_is_trivially_inhabited

end CriticalBarrier.GlobalRegularityFromG1
