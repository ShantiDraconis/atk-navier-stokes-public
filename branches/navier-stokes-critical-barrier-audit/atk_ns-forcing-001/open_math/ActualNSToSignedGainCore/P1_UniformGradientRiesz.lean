import open_math.ActualNSToSignedGainCore.P1_GradientRieszNineEntry

/-!
NS-FORCING-001 / uniform-in-time nine-entry Riesz payload.

The small-data signed-gain theorem needs one constant valid at every time.
A per-time payload is insufficient. This file records the exact stronger
material object required by the analytic chain.
-/

noncomputable section

namespace NSProducerFirst.P1Concrete

structure UniformGradientRieszPayload
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f) where
  C_CZ : ℝ
  hC_CZ : 0 ≤ C_CZ
  atTime :
    ∀ t : ℝ,
      GradientRieszNineEntryPayload s.velocity t
  uniform :
    ∀ t : ℝ,
      (atTime t).Cmax ≤ C_CZ

def UNIFORM_GRADIENT_RIESZ_OPEN_MATH
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f) : Prop :=
  Nonempty (UniformGradientRieszPayload s)

theorem uniformGradientRiesz_per_time
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    {s : SmoothNSState times ν f}
    (H : UNIFORM_GRADIENT_RIESZ_OPEN_MATH s)
    (t : ℝ) :
    GRADIENT_RIESZ_NINE_ENTRY_OPEN_MATH s.velocity t := by
  rcases H with ⟨P⟩
  exact ⟨P.atTime t⟩

theorem uniformGradientRiesz_constant
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    {s : SmoothNSState times ν f}
    (H : UNIFORM_GRADIENT_RIESZ_OPEN_MATH s) :
    ∃ C_CZ : ℝ, 0 ≤ C_CZ ∧
      ∀ t : ℝ, ((Classical.choice H).atTime t).Cmax ≤ C_CZ := by
  refine ⟨(Classical.choice H).C_CZ, (Classical.choice H).hC_CZ, ?_⟩
  exact (Classical.choice H).uniform

end NSProducerFirst.P1Concrete
