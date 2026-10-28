import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# LowProfileCoefficient

The positive time-constant low coefficient was formally refuted as a uniform T4
candidate because its integral grows like `T`.  A scaling-compatible repair is

  aLow(t) = R^2 * B * phi(R^2 t),

where `R` has frequency degree +1, `B` is scale invariant and `phi` is a
fixed dimensionless time profile.  Under `R -> lambda R`, this satisfies the
exact ThirdCoefficient law

  aLow_scaled(t) = lambda^2 aLow(lambda^2 t).

If `phi` has a finite dimensionless integral, the time change `s=R^2 t`
formally cancels the `R^2` prefactor.  The actual PDE estimate producing this
profile remains open.
-/

/-- Dynamic low-frequency profile coefficient. -/
def lowProfileCoefficient
    (R B : ℝ) (phi : ℝ → ℝ) (t : ℝ) : ℝ :=
  R^2 * B * phi (R^2 * t)

/-- Exact critical scaling when the cutoff scales as `R -> lambda R`. -/
theorem lowProfileCoefficient_critical_scaling
    (R B lambda t : ℝ) (phi : ℝ → ℝ) :
    lowProfileCoefficient (lambda * R) B phi t =
      lambda^2 * lowProfileCoefficient R B phi (lambda^2 * t) := by
  unfold lowProfileCoefficient
  ring_nf

/-- Nonnegativity follows from nonnegative amplitude data and profile. -/
theorem lowProfileCoefficient_nonnegative
    (R B t : ℝ) (phi : ℝ → ℝ)
    (hB : 0 ≤ B)
    (hphi : ∀ s, 0 ≤ phi s) :
    0 ≤ lowProfileCoefficient R B phi t := by
  unfold lowProfileCoefficient
  have hprofile : 0 ≤ phi (R^2 * t) := hphi _
  exact mul_nonneg (mul_nonneg (sq_nonneg R) hB) hprofile

/-- A profile-integral certificate isolates exactly the change-of-variables
statement needed for T4 without assuming it for arbitrary abstract integrals. -/
structure LowProfileIntegralCertificate
    (R B : ℝ) (phi : ℝ → ℝ) where
  totalProfileMass : ℝ
  hmass_nonnegative : 0 ≤ totalProfileMass
  fullTimeIntegral : ℝ
  hfullTimeIntegral : fullTimeIntegral = B * totalProfileMass

/-- Once the change-of-variables certificate exists, the low budget is
independent of the dimensional cutoff `R`. -/
theorem low_profile_budget_independent_of_cutoff
    (R B : ℝ) (phi : ℝ → ℝ)
    (h : LowProfileIntegralCertificate R B phi) :
    h.fullTimeIntegral = B * h.totalProfileMass :=
  h.hfullTimeIntegral

/-- The analytic route that would make this a real T3/T4 candidate. -/
structure LowProfileAnalyticFrontier where
  cutoff_from_initial_data_degree_one : Prop
  invariant_amplitude_factor : Prop
  profile_nonnegative : Prop
  profile_dimensionless : Prop
  profile_integrable : Prop
  PDE_low_block_bound_by_profile_times_Y : Prop
  change_of_variables_justified : Prop
  budget_initial_data_only : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_endpoint_reuse : Prop

end MPrivate.NS.ThirdCoefficient
