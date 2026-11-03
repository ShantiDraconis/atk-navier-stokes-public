import open_math.ActualNSToSignedGainCore.P1_StretchingPointwise
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
NS-FORCING-001 / L3 Holder closure for the vortex-stretching majorant.

This closes the purely functional-analysis step
  |omega| * |omega| * |grad u| : L1
from omega, grad u in L3.

No Calderon--Zygmund estimate is assumed or proved here.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

def p1LpNorm (p : ENNReal) (f : Space → ℝ) : ℝ :=
  (eLpNorm f p (volume : Measure Space)).toReal

theorem p1_scalar_product_bound
    {p q r : ENNReal} [ENNReal.HolderTriple p q r]
    {f g : Space → ℝ}
    (hf : MemLp f p volume) (hg : MemLp g q volume) :
    MemLp (fun x => f x * g x) r volume ∧
      p1LpNorm r (fun x => f x * g x) ≤
        p1LpNorm p f * p1LpNorm q g := by
  have hprod : MemLp (fun x => f x * g x) r volume := hg.mul' hf
  have hb :
      eLpNorm (fun x => f x * g x) r volume ≤
        eLpNorm f p volume * eLpNorm g q volume := by
    simpa using
      eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
        hf.aestronglyMeasurable hg.aestronglyMeasurable
        (fun a b : ℝ => a * b) 1
        (Filter.Eventually.of_forall fun _ => by simp [norm_mul])
  refine ⟨hprod, ?_⟩
  simpa only [p1LpNorm, ENNReal.toReal_mul] using
    ENNReal.toReal_mono
      (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) hb

/-- If omega and the velocity gradient are both in L3, then the exact
pointwise stretching majorant is integrable. -/
theorem stretchingMajorant_memLp_one_of_L3
    (u : VelocityField) (t : ℝ)
    (hω : MemLp (vorticity u t) 3 volume)
    (hD : MemLp (fun x => spatialDerivative u t x) 3 volume) :
    MemLp (stretchingMajorant u t) 1 volume := by
  letI h33 : ENNReal.HolderTriple (3 : ENNReal) 3 (3 / 2) := by
    constructor
    rw [ENNReal.inv_div (by norm_num) (by norm_num), div_eq_mul_inv, two_mul]
  have hω2 :
      MemLp
        (fun x => ‖vorticity u t x‖ * ‖vorticity u t x‖)
        (3 / 2) volume :=
    (p1_scalar_product_bound hω.norm hω.norm).1
  letI h313 : ENNReal.HolderTriple (3 / 2 : ENNReal) 3 1 := by
    constructor
    rw [ENNReal.inv_div (by norm_num) (by norm_num), div_eq_mul_inv, two_mul,
      ENNReal.inv_three_add_inv_three, inv_one]
  have hfinal :
      MemLp
        (fun x =>
          (‖vorticity u t x‖ * ‖vorticity u t x‖) *
            ‖spatialDerivative u t x‖)
        1 volume :=
    (p1_scalar_product_bound hω2 hD.norm).1
  simpa [stretchingMajorant, pow_two, mul_assoc] using hfinal

/-- Quantitative L3 Holder bound for the exact majorant. -/
theorem stretchingMajorant_lpNorm_one_le
    (u : VelocityField) (t : ℝ)
    (hω : MemLp (vorticity u t) 3 volume)
    (hD : MemLp (fun x => spatialDerivative u t x) 3 volume) :
    p1LpNorm 1 (stretchingMajorant u t) ≤
      p1LpNorm 3 (fun x => ‖vorticity u t x‖) ^ 2 *
        p1LpNorm 3 (fun x => ‖spatialDerivative u t x‖) := by
  letI h33 : ENNReal.HolderTriple (3 : ENNReal) 3 (3 / 2) := by
    constructor
    rw [ENNReal.inv_div (by norm_num) (by norm_num), div_eq_mul_inv, two_mul]
  obtain ⟨hω2, hω2b⟩ :=
    p1_scalar_product_bound
      (p := (3 : ENNReal)) (q := 3) (r := 3 / 2)
      hω.norm hω.norm
  letI h313 : ENNReal.HolderTriple (3 / 2 : ENNReal) 3 1 := by
    constructor
    rw [ENNReal.inv_div (by norm_num) (by norm_num), div_eq_mul_inv, two_mul,
      ENNReal.inv_three_add_inv_three, inv_one]
  have hfinal :=
    (p1_scalar_product_bound
      (p := (3 / 2 : ENNReal)) (q := 3) (r := 1)
      hω2 hD.norm).2
  change
    p1LpNorm 1
      (fun x => ‖vorticity u t x‖ ^ 2 * ‖spatialDerivative u t x‖) ≤ _
  have hω0 :
      0 ≤ p1LpNorm 3 (fun x => ‖vorticity u t x‖) := by
    exact ENNReal.toReal_nonneg
  calc
    p1LpNorm 1
        (fun x => ‖vorticity u t x‖ ^ 2 * ‖spatialDerivative u t x‖)
        = p1LpNorm 1
            (fun x =>
              (‖vorticity u t x‖ * ‖vorticity u t x‖) *
                ‖spatialDerivative u t x‖) := by
          congr 1
          funext x
          rw [pow_two]
    _ ≤ p1LpNorm (3 / 2)
          (fun x => ‖vorticity u t x‖ * ‖vorticity u t x‖) *
        p1LpNorm 3 (fun x => ‖spatialDerivative u t x‖) := hfinal
    _ ≤
        (p1LpNorm 3 (fun x => ‖vorticity u t x‖) *
          p1LpNorm 3 (fun x => ‖vorticity u t x‖)) *
        p1LpNorm 3 (fun x => ‖spatialDerivative u t x‖) := by
          gcongr
    _ =
        p1LpNorm 3 (fun x => ‖vorticity u t x‖) ^ 2 *
          p1LpNorm 3 (fun x => ‖spatialDerivative u t x‖) := by
          rw [pow_two]

#print axioms NSProducerFirst.P1Concrete.p1_scalar_product_bound
#print axioms NSProducerFirst.P1Concrete.stretchingMajorant_memLp_one_of_L3
#print axioms NSProducerFirst.P1Concrete.stretchingMajorant_lpNorm_one_le

end NSProducerFirst.P1Concrete
