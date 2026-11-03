import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# CrossCoefficientScalingCorrection

If a low-frequency velocity amplitude scales as

  U_L,lambda = lambda U_L,

then the candidate

  a_cross = U_L^2

has the exact ThirdCoefficient degree +2.  This is only a scaling certificate;
it does not prove the Young-remainder factorization or the L1 time budget.
-/

/-- Degree-one velocity amplitude. -/
def DegreeOneVelocityAmplitude (U UScaled lambda : ℝ) : Prop :=
  UScaled = lambda * U

/-- Candidate cross coefficient. -/
def crossCoefficientFromVelocity (U : ℝ) : ℝ := U^2

/-- Squaring a degree-one velocity amplitude gives degree +2. -/
theorem cross_velocity_square_scales_degree_two
    (U UScaled lambda : ℝ)
    (hU : DegreeOneVelocityAmplitude U UScaled lambda) :
    crossCoefficientFromVelocity UScaled =
      lambda^2 * crossCoefficientFromVelocity U := by
  unfold DegreeOneVelocityAmplitude at hU
  unfold crossCoefficientFromVelocity
  rw [hU]
  ring

/-- The unresolved analytic obligations for this candidate. -/
structure VelocityCrossCoefficientFrontier where
  low_velocity_Linf_defined : Prop
  low_velocity_degree_one : Prop
  young_remainder_factors_through_Y : Prop
  coefficient_nonnegative : Prop
  L1_time_budget : Prop
  budget_scale_invariant : Prop
  budget_initial_data_only : Prop
  no_endpoint_reuse : Prop
  no_supY : Prop
  no_Z_div_Y : Prop

end MPrivate.NS.ThirdCoefficient
