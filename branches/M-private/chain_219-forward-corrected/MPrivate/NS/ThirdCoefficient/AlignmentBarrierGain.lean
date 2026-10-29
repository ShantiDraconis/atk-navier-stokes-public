import Mathlib
import MPrivate.NS.ThirdCoefficient.AlignmentDefectFactorization
import MPrivate.NS.ThirdCoefficient.AlignmentDepletionInequality

namespace MPrivate.NS.ThirdCoefficient

/-!
# AlignmentBarrierGain

A dimensionless defect helps only if it is quantitatively small where the
critical amplitude is large. Merely multiplying a rejected amplitude by a
number in `[0,1]` does not automatically escape the old barrier.
-/

/-- A candidate coefficient reduces to a known amplitude barrier when it
uniformly dominates a fixed positive multiple of that amplitude. This is a
pure comparison predicate; it does not assert that the amplitude itself has a
Navier--Stokes spacetime budget. Positivity excludes the vacuous choice `c = 0`. -/
def ReducesToKnownBarrier (candidate amplitude : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * amplitude t ≤ candidate t

/-- If the alignment defect is bounded below, then the alignment coefficient
still dominates the corresponding multiple of the critical amplitude. -/
theorem defect_lower_bound_preserves_amplitude_multiple
    (A D c : ℝ)
    (hA : 0 ≤ A)
    (hD : c ≤ D) :
    c * A ≤ alignmentCoefficient A D := by
  unfold alignmentCoefficient
  simpa [mul_comm] using (mul_le_mul_of_nonneg_right hD hA)

/-- Therefore a uniformly positive defect cannot by itself create an escape
from a rejected amplitude barrier. -/
theorem alignment_reduces_to_amplitude_if_defect_bounded_below
    (A D : ℝ → ℝ)
    (c : ℝ)
    (hc : 0 < c)
    (hA : ∀ t, 0 ≤ A t)
    (hD : ∀ t, c ≤ D t) :
    ReducesToKnownBarrier
      (fun t => alignmentCoefficient (A t) (D t)) A := by
  refine ⟨c, hc, ?_⟩
  intro t
  exact defect_lower_bound_preserves_amplitude_multiple (A t) (D t) c (hA t) (hD t)

/-- Genuine pointwise depletion relative to the amplitude requires only a
positive amplitude and a defect strictly below one at the point in question. -/
theorem strict_defect_strictly_reduces_positive_amplitude
    (A D : ℝ)
    (hA : 0 < A)
    (hD1 : D < 1) :
    alignmentCoefficient A D < A := by
  unfold alignmentCoefficient
  nlinarith

/-- Endpoint diagnostics: `D=0` kills the factored term, while `D=1` gives no
improvement. The unresolved PDE bridge is to derive useful spacetime control of
`D` from actual Navier--Stokes dynamics.  The fields below are audit obligations,
not a proof merely by construction of the record. -/
structure AlignmentGainFrontier where
  actual_solution_class_identified : Prop
  actual_alignment_block_identified : Prop
  critical_amplitude_identified : Prop
  defect_identified_from_actual_geometry : Prop
  defect_nonnegative : Prop
  defect_at_most_one : Prop
  defect_dimensionless : Prop
  defect_measurable : Prop
  critical_amplitude_measurable : Prop
  signed_factorization : Prop
  defect_strict_gain_on_relevant_set : Prop
  defect_spacetime_budget : Prop
  budget_uniform_for_every_T_below_Tstar : Prop
  maximal_lifetime_is_actual_solution_lifetime : Prop
  maximal_lifetime_positive : Prop
  passage_to_maximal_interval_justified : Prop
  derived_from_actual_NS : Prop
  budget_scale_invariant : Prop
  budget_initial_data_only : Prop
  constants_uniform_in_time : Prop
  constants_uniform_in_cutoff_and_shells : Prop
  cutoff_scale_covariant : Prop
  cutoff_independent_of_future_solution : Prop
  same_viscosity_as_enstrophy_balance : Prop
  no_hidden_time_length_factor : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_future_critical_norm : Prop
  no_endpoint_reuse : Prop
  no_maximal_time_value : Prop
  no_uncontrolled_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient
