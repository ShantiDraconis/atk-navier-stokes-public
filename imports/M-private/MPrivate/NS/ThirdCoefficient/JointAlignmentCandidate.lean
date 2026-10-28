import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# JointAlignmentCandidate

After the direction-only counterexample, a viable geometric diagnostic must
retain information about positive strain coupling.  We therefore keep a joint
quantity

  Qjoint = Qdir + alpha * Qstrain,

with `alpha>0`.  This file proves only algebraic facts about the joint quantity;
no coercive evolution or NSE depletion theorem is asserted.
-/

/-- Joint geometric diagnostic. -/
def jointAlignment
    (Qdir Qstrain alpha : ℝ) : ℝ :=
  Qdir + alpha * Qstrain

/-- Nonnegative pieces and positive alpha give a nonnegative joint diagnostic. -/
theorem jointAlignment_nonnegative
    (Qdir Qstrain alpha : ℝ)
    (hDir : 0 ≤ Qdir)
    (hStrain : 0 ≤ Qstrain)
    (hAlpha : 0 ≤ alpha) :
    0 ≤ jointAlignment Qdir Qstrain alpha := by
  unfold jointAlignment
  positivity

/-- If alpha is strictly positive, a zero joint diagnostic with nonnegative
components forces both components to vanish. -/
theorem jointAlignment_zero_forces_both_zero
    (Qdir Qstrain alpha : ℝ)
    (hDir : 0 ≤ Qdir)
    (hStrain : 0 ≤ Qstrain)
    (hAlpha : 0 < alpha)
    (hZero : jointAlignment Qdir Qstrain alpha = 0) :
    Qdir = 0 ∧ Qstrain = 0 := by
  unfold jointAlignment at hZero
  have hWeighted : 0 ≤ alpha * Qstrain := mul_nonneg (le_of_lt hAlpha) hStrain
  constructor
  · nlinarith
  · have hProd : alpha * Qstrain = 0 := by nlinarith
    exact (mul_eq_zero.mp hProd).resolve_left (ne_of_gt hAlpha)

/-- If both diagnostics are scale invariant and alpha is dimensionless, the
joint diagnostic is scale invariant. -/
theorem jointAlignment_scale_invariant
    (Qdir QdirScaled Qstrain QstrainScaled alpha : ℝ)
    (hDir : QdirScaled = Qdir)
    (hStrain : QstrainScaled = Qstrain) :
    jointAlignment QdirScaled QstrainScaled alpha =
      jointAlignment Qdir Qstrain alpha := by
  rw [hDir, hStrain]

/-- Analytic bridge still missing after defining the correct joint object. -/
structure JointAlignmentFrontier where
  Qdir_derived_from_flow : Prop
  Qstrain_derived_from_positive_strain_coupling : Prop
  alpha_fixed_independently_of_target : Prop
  coercive_evolution_for_Qjoint : Prop
  commutator_transport_absorption : Prop
  exceptional_tail_control : Prop
  strict_margin : Prop
  L1_defect_budget : Prop
  signed_depletion_conclusion : Prop

end MPrivate.NS.ThirdCoefficient
