import open_math.ActualNSToSignedGainCore.P1_MixedPartials
import open_math.ActualNSToSignedGainCore.P1_GradientRieszNineEntry
import open_math.ActualNSToSignedGainCore.P1_RieszH1ConcreteRoute

/-!
NS-FORCING-001 / complete analytic slice data for the concrete H1 route.

Important: on R3, L3 does not imply L2.  The H1 compression route therefore
requires explicit finite-enstrophy / finite-palinstrophy data in addition to
the L3 vorticity premise.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

/-- Exact analytic data required by the concrete H1-to-L3 route at one time. -/
structure NSAnalyticSliceData
    (u : VelocityField) (t : ℝ) where
  velocity_smooth :
    ContDiff ℝ 2 (fun x : Space => u (t, x))
  velocity_L2 :
    MemLp (fun x : Space => u (t, x)) 2 (volume : Measure Space)
  divergence_free :
    ∀ x : Space, spatialDivergence u t x = 0
  vorticity_L2 :
    MemLp (vorticity u t) 2 (volume : Measure Space)
  vorticity_L3 :
    MemLp (vorticity u t) 3 (volume : Measure Space)
  vorticity_derivative_L2 :
    MemLp
      (fderiv ℝ (vorticity u t))
      2 (volume : Measure Space)

/-- Material local vector-calculus law, separated from harmonic analysis. -/
def LOCAL_DIVCURL_MATERIAL
    (u : VelocityField) (t : ℝ) : Prop :=
  ∀ x : Space,
    spatialLaplacian u t x = - curlVorticity u t x

/-- The exact Fourier/Biot-Savart reconstruction target: all nine gradient
entries receive concrete L3 controls from vorticity. -/
def BIOT_SAVART_NINE_ENTRY_MATERIAL
    (u : VelocityField) (t : ℝ) : Prop :=
  GRADIENT_RIESZ_NINE_ENTRY_OPEN_MATH u t

/-- Complete material slice package before the nonlinear stretching step. -/
structure NSGradientMaterialSlice
    (u : VelocityField) (t : ℝ) where
  analytic : NSAnalyticSliceData u t
  divCurl : LOCAL_DIVCURL_MATERIAL u t
  rieszNine :
    GradientRieszNineEntryPayload u t

/-- The H1 route explicitly exposes the extra L2 information; no hidden
L3->L2 implication is used. -/
theorem analyticSlice_exposes_H1_inputs
    {u : VelocityField} {t : ℝ}
    (h : NSAnalyticSliceData u t) :
    MemLp (vorticity u t) 2 (volume : Measure Space) ∧
    MemLp (fderiv ℝ (vorticity u t)) 2 (volume : Measure Space) ∧
    MemLp (vorticity u t) 3 (volume : Measure Space) :=
  ⟨h.vorticity_L2, h.vorticity_derivative_L2, h.vorticity_L3⟩

end NSProducerFirst.P1Concrete
