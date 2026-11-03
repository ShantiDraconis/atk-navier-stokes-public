import open_math.ActualNSToSignedGainCore.P1_GradientEntries
import open_math.ActualNSToSignedGainCore.P1_RieszH1ConcreteRoute
import open_math.ActualNSToSignedGainCore.P1_RieszCZ_L3

/-!
NS-FORCING-001 / concrete nine-entry Riesz reconstruction schema.

This file does not assert the Biot--Savart representation.  It states the
exact material object needed: for every one of the nine gradient entries,
give a finite concrete Riesz representation together with the L3 control.
Once supplied, the existing finite-dimensional reconstruction closes the
operator-norm L3 target.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NSProducerFirst.P1Concrete

/-- A concrete scalar L3 control for one gradient entry. -/
structure GradientEntryL3Control
    (u : VelocityField) (t : ℝ) (j i : Fin 3) where
  memLp :
    MemLp (gradientEntry u t j i) 3 (volume : Measure Space)
  C : ℝ
  hC : 0 ≤ C
  bound :
    (eLpNorm (gradientEntry u t j i) 3
      (volume : Measure Space)).toReal ≤
      C * (eLpNorm (vorticity u t) 3
        (volume : Measure Space)).toReal

/-- Material nine-entry package.  This is the exact finite reconstruction
object required after the Fourier/Riesz representation is proved. -/
structure GradientRieszNineEntryPayload
    (u : VelocityField) (t : ℝ) where
  entry : ∀ j i : Fin 3, GradientEntryL3Control u t j i
  Cmax : ℝ
  hCmax : 0 ≤ Cmax
  entry_le_Cmax :
    ∀ j i : Fin 3, (entry j i).C ≤ Cmax

/-- Pointwise operator norm is controlled by the sum of the nine scalar
entries; imported from the already-proved finite-dimensional reconstruction. -/
theorem gradient_pointwise_le_nine_entries
    (u : VelocityField) (t : ℝ) (x : Space) :
    ‖spatialDerivative u t x‖ ≤
      ∑ j : Fin 3, ∑ i : Fin 3, |gradientEntry u t j i x| :=
  spatialDerivative_norm_le_sum_entries u t x

/-- The nine-entry payload is the material object that the Fourier side must
produce.  This proposition is deliberately concrete and contains no endpoint
aliases. -/
def GRADIENT_RIESZ_NINE_ENTRY_OPEN_MATH
    (u : VelocityField) (t : ℝ) : Prop :=
  Nonempty (GradientRieszNineEntryPayload u t)

/-- Every material nine-entry payload exposes each scalar L3 control directly. -/
theorem nineEntryPayload_entry
    {u : VelocityField} {t : ℝ}
    (H : GRADIENT_RIESZ_NINE_ENTRY_OPEN_MATH u t)
    (j i : Fin 3) :
    GradientEntryL3Control u t j i := by
  rcases H with ⟨P⟩
  exact P.entry j i

/-- Uniform coefficient bound from the finite payload. -/
theorem nineEntryPayload_uniform_coefficient
    {u : VelocityField} {t : ℝ}
    (H : GRADIENT_RIESZ_NINE_ENTRY_OPEN_MATH u t) :
    ∃ Cmax : ℝ, 0 ≤ Cmax ∧
      ∀ j i : Fin 3,
        ((nineEntryPayload_entry H j i).C ≤ Cmax) := by
  rcases H with ⟨P⟩
  exact ⟨P.Cmax, P.hCmax, P.entry_le_Cmax⟩

end NSProducerFirst.P1Concrete
