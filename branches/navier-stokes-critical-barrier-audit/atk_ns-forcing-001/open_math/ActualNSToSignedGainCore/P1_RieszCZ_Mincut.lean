import Mathlib.Analysis.Distribution.FourierMultiplier
import open_math.ActualNSToSignedGainCore.P1_RieszCZ_L3

/-!
NS-FORCING-001 / exact Riesz-CZ mincut.

Mathlib supplies Fourier-multiplier infrastructure but no ready-made strong
L^3 Calderon--Zygmund theorem for the Riesz multipliers.  This file freezes
all downstream algebra and exposes exactly one analytic obligation: strong
L^3 boundedness of the concrete Riesz multiplier family.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

/-- Scalar Riesz symbol component xi_j / |xi|, with the origin sent to zero. -/
def p1RieszSymbol (j : Fin 3) (ξ : Space) : ℝ :=
  if h : ‖ξ‖ = 0 then 0 else ξ j / ‖ξ‖

theorem p1RieszSymbol_zero (j : Fin 3) :
    p1RieszSymbol j 0 = 0 := by
  simp [p1RieszSymbol]

/-- Pointwise boundedness of the scalar Riesz symbol. -/
theorem abs_p1RieszSymbol_le_one (j : Fin 3) (ξ : Space) :
    |p1RieszSymbol j ξ| ≤ 1 := by
  by_cases h : ‖ξ‖ = 0
  · simp [p1RieszSymbol, h]
  · simp only [p1RieszSymbol, h, dif_neg]
    have hcoord : |ξ j| ≤ ‖ξ‖ := by
      simpa [Real.norm_eq_abs] using norm_apply_le_norm ξ j
    have hnorm : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm h)
    rw [abs_div, abs_of_nonneg (norm_nonneg ξ)]
    exact (div_le_one hnorm).2 hcoord

/--
The exact analytic leaf still required by the concrete NS chain:
strong L^3 boundedness of the fixed-dimensional Riesz/CZ reconstruction.
No Navier--Stokes regularity conclusion appears in this proposition.
-/
def P1_RIESZ_CZ_L3_OPEN_MATH : Prop :=
  ∀ (u : VelocityField) (t : ℝ),
    MemLp (fun x => u (t, x)) 2 (volume : Measure Space) →
    (∀ x, spatialDivergence u t x = 0) →
    MemLp (vorticity u t) 3 (volume : Measure Space) →
    ∃ C_CZ : ℝ,
      0 ≤ C_CZ ∧
      MemLp (fun x => spatialDerivative u t x) 3 (volume : Measure Space) ∧
      (eLpNorm (fun x => spatialDerivative u t x) 3
          (volume : Measure Space)).toReal ≤
        C_CZ *
          (eLpNorm (vorticity u t) 3
            (volume : Measure Space)).toReal

/-- The mincut is definitionally the theorem currently carrying the material
sorry in P1_RieszCZ_L3.  Once this one producer is supplied, no new endpoint
parameter is introduced. -/
theorem p1_rieszCZ_L3_of_mincut
    (H : P1_RIESZ_CZ_L3_OPEN_MATH)
    (u : VelocityField)
    (t : ℝ)
    (hu2 : MemLp (fun x => u (t, x)) 2 (volume : Measure Space))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hω3 : MemLp (vorticity u t) 3 (volume : Measure Space)) :
    ∃ C_CZ : ℝ,
      0 ≤ C_CZ ∧
      MemLp (fun x => spatialDerivative u t x) 3 (volume : Measure Space) ∧
      (eLpNorm (fun x => spatialDerivative u t x) 3
          (volume : Measure Space)).toReal ≤
        C_CZ *
          (eLpNorm (vorticity u t) 3
            (volume : Measure Space)).toReal :=
  H u t hu2 hdiv hω3

/-- Exactness: the currently stated concrete theorem provides the mincut. -/
theorem mincut_of_p1_rieszCZ_L3 :
    P1_RIESZ_CZ_L3_OPEN_MATH := by
  intro u t hu2 hdiv hω3
  exact p1_rieszCZ_L3 u t hu2 hdiv hω3

#print axioms NSProducerFirst.P1Concrete.abs_p1RieszSymbol_le_one
#print axioms NSProducerFirst.P1Concrete.p1_rieszCZ_L3_of_mincut
#print axioms NSProducerFirst.P1Concrete.mincut_of_p1_rieszCZ_L3

end NSProducerFirst.P1Concrete
