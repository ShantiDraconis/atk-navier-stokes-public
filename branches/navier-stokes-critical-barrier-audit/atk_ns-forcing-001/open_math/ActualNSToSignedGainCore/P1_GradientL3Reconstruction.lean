import open_math.ActualNSToSignedGainCore.P1_GradientRieszNineEntry
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
NS-FORCING-001 / nine scalar L3 entries reconstruct the full gradient in L3.

Pure finite-dimensional / Lp bookkeeping. No Fourier theorem is assumed here
beyond the supplied nine-entry material payload.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NSProducerFirst.P1Concrete

/-- Scalar absolute-value majorant of the nine gradient entries. -/
def gradientEntryMajorant
    (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, ∑ i : Fin 3, |gradientEntry u t j i x|

theorem gradientEntryMajorant_memLp
    {u : VelocityField} {t : ℝ}
    (H : GRADIENT_RIESZ_NINE_ENTRY_OPEN_MATH u t) :
    MemLp (gradientEntryMajorant u t) 3 (volume : Measure Space) := by
  rcases H with ⟨P⟩
  unfold gradientEntryMajorant
  apply memLp_finsetSum' Finset.univ
  intro j hj
  apply memLp_finsetSum' Finset.univ
  intro i hi
  simpa [Real.norm_eq_abs] using (P.entry j i).memLp.norm

/-- Nine scalar L3 controls plus measurability of the concrete gradient imply
the full operator-valued gradient is in L3. -/
theorem spatialDerivative_memLp_three_of_nine_entries
    {u : VelocityField} {t : ℝ}
    (H : GRADIENT_RIESZ_NINE_ENTRY_OPEN_MATH u t)
    (hmeas :
      AEStronglyMeasurable
        (fun x : Space => spatialDerivative u t x)
        (volume : Measure Space)) :
    MemLp
      (fun x : Space => spatialDerivative u t x)
      3
      (volume : Measure Space) := by
  apply MemLp.of_le (gradientEntryMajorant_memLp H) hmeas
  exact Eventually.of_forall fun x => by
    simpa [gradientEntryMajorant] using
      spatialDerivative_norm_le_sum_entries u t x

#print axioms NSProducerFirst.P1Concrete.gradientEntryMajorant_memLp
#print axioms NSProducerFirst.P1Concrete.spatialDerivative_memLp_three_of_nine_entries

end NSProducerFirst.P1Concrete
