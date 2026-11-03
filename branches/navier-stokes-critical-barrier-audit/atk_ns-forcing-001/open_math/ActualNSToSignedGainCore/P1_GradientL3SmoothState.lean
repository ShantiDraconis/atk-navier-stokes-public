import open_math.ActualNSToSignedGainCore.P1_DivCurlIdentity
import open_math.ActualNSToSignedGainCore.P1_GradientL3Reconstruction

/-!
NS-FORCING-001 / smooth-state measurability bridge.

For a concrete SmoothNSState, the spatial derivative is continuous at fixed
time, hence strongly measurable. This removes the auxiliary measurability
premise from the nine-entry L3 reconstruction.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

theorem smoothNSState_spatialDerivative_aestronglyMeasurable
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (ht : t ∈ times) :
    AEStronglyMeasurable
      (fun x : Space => spatialDerivative s.velocity t x)
      (volume : Measure Space) := by
  have hcont :
      Continuous
        (fderiv ℝ (fun x : Space => s.velocity (t, x))) :=
    (spatialSlice_contDiff s ht).continuous_fderiv (by simp)
  simpa [spatialDerivative] using hcont.aestronglyMeasurable

theorem smoothNSState_spatialDerivative_memLp_three_of_nine_entries
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (ht : t ∈ times)
    (H : GRADIENT_RIESZ_NINE_ENTRY_OPEN_MATH s.velocity t) :
    MemLp
      (fun x : Space => spatialDerivative s.velocity t x)
      3
      (volume : Measure Space) :=
  spatialDerivative_memLp_three_of_nine_entries H
    (smoothNSState_spatialDerivative_aestronglyMeasurable s ht)

#print axioms NSProducerFirst.P1Concrete.smoothNSState_spatialDerivative_aestronglyMeasurable
#print axioms NSProducerFirst.P1Concrete.smoothNSState_spatialDerivative_memLp_three_of_nine_entries

end NSProducerFirst.P1Concrete
