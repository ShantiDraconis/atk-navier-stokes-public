import open_math.ActualNSToSignedGainCore.P1_ConcreteObservables

/-!
NS-FORCING-001 / pointwise vortex-stretching bound.

No PDE closure assumption, no axiom, no sorry.
-/

noncomputable section

namespace NSProducerFirst.P1Concrete

/-- Pointwise Cauchy--Schwarz/operator-norm control of the signed
vortex-stretching density. -/
theorem abs_stretchingDensity_le
    (u : VelocityField) (t : ℝ) (x : Space) :
    |stretchingDensity u t x| ≤
      ‖vorticity u t x‖ ^ 2 * ‖spatialDerivative u t x‖ := by
  unfold stretchingDensity
  have hinner :
      |@inner ℝ Space _ (vorticity u t x)
        (spatialDerivative u t x (vorticity u t x))| ≤
        ‖vorticity u t x‖ *
          ‖spatialDerivative u t x (vorticity u t x)‖ := by
    simpa [Real.norm_eq_abs] using
      abs_real_inner_le_norm
        (vorticity u t x)
        (spatialDerivative u t x (vorticity u t x))
  have hop :
      ‖spatialDerivative u t x (vorticity u t x)‖ ≤
        ‖spatialDerivative u t x‖ * ‖vorticity u t x‖ :=
    ContinuousLinearMap.le_opNorm _ _
  calc
    |@inner ℝ Space _ (vorticity u t x)
        (spatialDerivative u t x (vorticity u t x))|
        ≤ ‖vorticity u t x‖ *
            ‖spatialDerivative u t x (vorticity u t x)‖ := hinner
    _ ≤ ‖vorticity u t x‖ *
          (‖spatialDerivative u t x‖ * ‖vorticity u t x‖) := by
          gcongr
    _ = ‖vorticity u t x‖ ^ 2 * ‖spatialDerivative u t x‖ := by
          ring

/-- The unsigned scalar majorant which is the exact input for the L3 Holder
step. -/
def stretchingMajorant
    (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  ‖vorticity u t x‖ ^ 2 * ‖spatialDerivative u t x‖

theorem stretchingDensity_le_majorant
    (u : VelocityField) (t : ℝ) (x : Space) :
    stretchingDensity u t x ≤ stretchingMajorant u t x := by
  exact (le_abs_self _).trans (abs_stretchingDensity_le u t x)

theorem stretchingMajorant_nonneg
    (u : VelocityField) (t : ℝ) (x : Space) :
    0 ≤ stretchingMajorant u t x := by
  exact mul_nonneg (sq_nonneg _) (norm_nonneg _)

#print axioms NSProducerFirst.P1Concrete.abs_stretchingDensity_le
#print axioms NSProducerFirst.P1Concrete.stretchingDensity_le_majorant
#print axioms NSProducerFirst.P1Concrete.stretchingMajorant_nonneg

end NSProducerFirst.P1Concrete
