import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# LowFrequencyScaleCovariance

Audit-safe algebraic certificates for the low-frequency part of a ThirdCoefficient.

The point is to separate two facts:
1. a low-frequency coefficient may be easy to estimate at a chosen cutoff;
2. a fixed dimensional cutoff is not itself Navier--Stokes scale covariant.

No PDE estimate is asserted here.
-/

/-- A cutoff transforms covariantly under NS scaling when `R -> lambda R`. -/
def CutoffScaleCovariant (Rscaled R lambda : ℝ) : Prop :=
  Rscaled = lambda * R

/-- A model low-frequency coefficient with the expected `R^2` homogeneity. -/
def lowModel (R A : ℝ) : ℝ := R^2 * A

/-- If the amplitude factor is scale invariant and the cutoff scales as `lambda R`,
then the model coefficient scales like `lambda^2`. -/
theorem lowModel_scales_critically
    (R A lambda : ℝ) :
    lowModel (lambda * R) A = lambda^2 * lowModel R A := by
  unfold lowModel
  ring

/-- Holding a nonzero cutoff fixed cannot reproduce critical scaling for all lambda.
This is a purely algebraic warning against treating a dimensional fixed `R0` as a
scale-covariant construction. -/
theorem fixed_nonzero_cutoff_not_critical
    {R A : ℝ}
    (hR : R ≠ 0)
    (hA : A ≠ 0) :
    ¬ (∀ lambda : ℝ, 0 < lambda -> lowModel R A = lambda^2 * lowModel R A) := by
  intro h
  have h2 := h 2 (by norm_num)
  unfold lowModel at h2
  have hRA : R^2 * A ≠ 0 := mul_ne_zero (pow_ne_zero 2 hR) hA
  have hz : R^2 * A = 0 := by
    nlinarith [h2]
  exact hRA hz

/-- A scale-invariant initial budget can be used as an amplitude parameter without
creating an immediate homogeneity contradiction.  This theorem only certifies the
homogeneity bookkeeping; it does not prove an NSE bound by that budget. -/
def ScaleInvariantInitialBudget
    (B : ℝ -> ℝ) : Prop :=
  ∀ lambda x, 0 < lambda -> B (lambda * x) = B x

/-- Scaling consistency alone is not an admissible low-frequency closure.  The
actual route must additionally discharge these analytic and circularity gates. -/
structure LowFrequencyScalingFrontier where
  cutoff_positive : Prop
  cutoff_degree_one : Prop
  amplitude_degree_zero : Prop
  coefficient_degree_two : Prop
  cutoff_initial_data_only : Prop
  cutoff_independent_of_Tstar : Prop
  cutoff_independent_of_future_target : Prop
  low_pointwise_PDE_estimate : Prop
  low_coefficient_nonnegative : Prop
  low_coefficient_measurable : Prop
  low_L1_budget_if_not_absorbed : Prop
  direct_absorption_uses_extra_valid_structure_if_claimed : Prop
  no_false_reverse_lowpass_poincare : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_endpoint_reuse : Prop

end MPrivate.NS.ThirdCoefficient
