import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# JointEvolutionAbsorption

Algebraic core of the historical G1a--G1d programme, rewritten without hidden
analytic assumptions.  A successful joint quantity `Q` should satisfy

  Q' + viscous * Q <= Comm + Transport + Tail + lower * Q.

Comm/Transport/Tail may each spend a fraction of the viscous term.  Their total
fraction must remain strictly below one; every leftover lower-order term must
be collected into an independently integrable multiplier.
-/

/-- Signed/cost decomposition of the right-hand side of a joint evolution. -/
structure JointEvolutionTerms where
  qPrime : ℝ
  q : ℝ
  viscous : ℝ
  commutator : ℝ
  transport : ℝ
  tail : ℝ
  lowerMultiplier : ℝ

/-- Raw joint evolution inequality. -/
def JointEvolutionInequality (E : JointEvolutionTerms) : Prop :=
  E.qPrime + E.viscous * E.q ≤
    E.commutator + E.transport + E.tail + E.lowerMultiplier * E.q

/-- One cost term is absorbed up to a residual multiplier. -/
def CostAbsorption
    (cost gamma viscous q b : ℝ) : Prop :=
  cost ≤ gamma * viscous * q + b * q

/-- Three analytic costs share the same viscous budget. -/
theorem three_costs_absorb_with_shared_budget
    (comm transport tail viscous q
      gComm gTransport gTail
      bComm bTransport bTail : ℝ)
    (hC : CostAbsorption comm gComm viscous q bComm)
    (hT : CostAbsorption transport gTransport viscous q bTransport)
    (hTail : CostAbsorption tail gTail viscous q bTail) :
    comm + transport + tail ≤
      (gComm + gTransport + gTail) * viscous * q +
      (bComm + bTransport + bTail) * q := by
  unfold CostAbsorption at hC hT hTail
  nlinarith

/-- Full reduction of the raw evolution inequality to a strict-margin form. -/
theorem joint_evolution_after_absorption
    (E : JointEvolutionTerms)
    (gComm gTransport gTail bComm bTransport bTail : ℝ)
    (hE : JointEvolutionInequality E)
    (hC : CostAbsorption E.commutator gComm E.viscous E.q bComm)
    (hT : CostAbsorption E.transport gTransport E.viscous E.q bTransport)
    (hTail : CostAbsorption E.tail gTail E.viscous E.q bTail) :
    E.qPrime +
      (1 - (gComm + gTransport + gTail)) * E.viscous * E.q ≤
      (bComm + bTransport + bTail + E.lowerMultiplier) * E.q := by
  unfold JointEvolutionInequality at hE
  have hab := three_costs_absorb_with_shared_budget
    E.commutator E.transport E.tail E.viscous E.q
    gComm gTransport gTail bComm bTransport bTail hC hT hTail
  nlinarith

/-- Strict shared absorption budget. -/
def JointAbsorptionMargin
    (gComm gTransport gTail : ℝ) : Prop :=
  0 ≤ gComm ∧ 0 ≤ gTransport ∧ 0 ≤ gTail ∧
  gComm + gTransport + gTail < 1

/-- A strict shared budget leaves a positive fraction of the viscous term. -/
theorem joint_absorption_leaves_positive_fraction
    (gComm gTransport gTail : ℝ)
    (h : JointAbsorptionMargin gComm gTransport gTail) :
    0 < 1 - (gComm + gTransport + gTail) := by
  rcases h with ⟨_, _, _, hlt⟩
  linarith

/-- Combined multiplier to be sent to T4. -/
def jointLowerMultiplier
    (bComm bTransport bTail lower : ℝ) : ℝ :=
  bComm + bTransport + bTail + lower

/-- Nothing in the algebra proves integrability of this multiplier. -/
structure JointEvolutionAnalyticFrontier where
  q_joint_derived : Prop
  raw_evolution_from_actual_NS : Prop
  commutator_absorption : Prop
  transport_absorption : Prop
  tail_absorption : Prop
  strict_shared_budget : Prop
  lower_multiplier_nonnegative : Prop
  lower_multiplier_L1 : Prop
  lower_multiplier_non_circular : Prop
  epsilon_limit_passage : Prop

end MPrivate.NS.ThirdCoefficient
