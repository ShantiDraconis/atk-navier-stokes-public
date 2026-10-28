import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# AlignmentAmplitudeScalingCorrection

For Navier--Stokes scaling `u_lambda(x,t)=lambda u(lambda x,lambda^2 t)`,
strain scales pointwise with degree +2. Therefore any homogeneous spatial norm
of strain with zero spatial derivative index such as BMO or homogeneous
`B^0_{infinity,infinity}` inherits degree +2 from amplitude scaling.

Consequently, in an alignment coefficient

  a_align = Acrit * D,

with dimensionless angular defect `D`, the natural strain amplitude `Acrit`
already supplies the required ThirdCoefficient degree +2. It should not be
labeled scale invariant.

This file encodes the homogeneity algebra abstractly; it does not formalize BMO
or Besov spaces themselves.
-/

/-- Degree-two amplitude, modeling a strain norm. -/
def DegreeTwoAmplitude (A AScaled lambda : ℝ) : Prop :=
  AScaled = lambda^2 * A

/-- Dimensionless defect. -/
def InvariantDefect (D DScaled : ℝ) : Prop :=
  DScaled = D

/-- Alignment coefficient from a degree-two amplitude and invariant defect. -/
def correctedAlignmentCoefficient (A D : ℝ) : ℝ := A * D

/-- The product has exactly the required degree +2. -/
theorem corrected_alignment_coefficient_scales_degree_two
    (A AScaled D DScaled lambda : ℝ)
    (hA : DegreeTwoAmplitude A AScaled lambda)
    (hD : InvariantDefect D DScaled) :
    correctedAlignmentCoefficient AScaled DScaled =
      lambda^2 * correctedAlignmentCoefficient A D := by
  unfold DegreeTwoAmplitude at hA
  unfold InvariantDefect at hD
  unfold correctedAlignmentCoefficient
  rw [hA, hD]
  ring

/-- If both amplitude and defect were incorrectly declared invariant, the
coefficient would have degree zero rather than the required degree two. -/
theorem invariant_times_invariant_wrong_degree_witness :
    let A : ℝ := 1
    let D : ℝ := 1
    let lambda : ℝ := 2
    A * D ≠ lambda^2 * (A * D) := by
  norm_num

/-- Audit classification for common alignment amplitudes. -/
inductive AlignmentAmplitudeClass where
  | strainBMO_degreeTwo
  | strainBesov0InfInf_degreeTwo
  | dimensionlessGeometry_degreeZero
  | unknownNeedsProof
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
