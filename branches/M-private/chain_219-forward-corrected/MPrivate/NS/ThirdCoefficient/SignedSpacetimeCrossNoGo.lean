import Mathlib
import MPrivate.NS.ThirdCoefficient.EightTermSignedGrouping
import MPrivate.NS.ThirdCoefficient.ScalingClassifier

namespace MPrivate.NS.ThirdCoefficient

/-!
# SignedSpacetimeCrossNoGo

Two shortcuts that must not be used in the signed spacetime cross route:

1. the signed mixed Bony block is not identically zero merely because some
   configurations exhibit cancellation;
2. kinetic energy cannot be substituted for enstrophy through a universal
   scale-invariant bound on R^3, since their Navier--Stokes scaling degrees are
   opposite.

These are audit guards.  They do not rule out a genuine quantitative signed
shell estimate derived from the actual NSE dynamics.
-/

/-- The mixed signed block can cancel for special data, but is not an
identically vanishing algebraic expression. -/
theorem mixed_signed_block_nonzero_witness :
    mixedSignedBlock 1 1 1 1 = 6 := by
  norm_num [mixedSignedBlock, VLLHpair, VLHH, VHLL, VHLHpair]

/-- Hence the existing signed grouping alone cannot justify a universal
`mixedSignedBlock = 0` telescoping rule. -/
theorem not_universal_mixed_block_cancellation :
    ¬ (∀ sL sH wL wH : ℝ, mixedSignedBlock sL sH wL wH = 0) := by
  intro h
  have hz := h 1 1 1 1
  rw [mixed_signed_block_nonzero_witness] at hz
  norm_num at hz

/-- Scaling obstruction to replacing enstrophy by kinetic energy.
Under NS scaling, enstrophy scales as `lambda * Y`, while kinetic energy scales
as `E / lambda`.  Whenever `C*E < lambda^2*Y`, the putative scale-invariant
bound `lambda*Y <= C*(E/lambda)` is impossible. -/
theorem energy_cannot_control_enstrophy_at_incompatible_scale
    (Y E C lambda : ℝ)
    (hlambda : 0 < lambda)
    (hbad : C * E < lambda ^ 2 * Y) :
    ¬ (lambda * Y ≤ C * (E / lambda)) := by
  intro h
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hlambda)
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda
  have hright : lambda * (C * (E / lambda)) = C * E := by
    field_simp [hlambda_ne]
  have hleft : lambda * (lambda * Y) = lambda ^ 2 * Y := by ring
  rw [hleft, hright] at hmul
  exact (not_lt_of_ge hmul) hbad

/-- Explicit audit register for any future proof of signed shell cancellation. -/
structure SignedCancellationAuditGuards where
  no_universal_cancellation_inferred_from_special_witness : Prop
  dyadic_coefficients_derived_from_actual_projectors : Prop
  divergence_free_identity_proved_for_actual_blocks : Prop
  telescoping_identity_proved_before_limit_passage : Prop
  no_energy_for_enstrophy_substitution : Prop
  enstrophy_scaling_degree_one_respected : Prop
  kinetic_energy_scaling_degree_minus_one_respected : Prop
  no_pointwise_lowpass_reverse_poincare : Prop
  no_triangle_inequality_before_signed_grouping : Prop
  quantitative_gain_not_inferred_from_algebraic_identity_alone : Prop

end MPrivate.NS.ThirdCoefficient
