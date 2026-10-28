import Mathlib
import MPrivate.NS.ThirdCoefficient.CrossTermYoungAbsorption
import MPrivate.NS.ThirdCoefficient.CrossVelocityFactorization

namespace MPrivate.NS.ThirdCoefficient

/-!
# CrossRemainderFactorsThroughYGoal

Audit-safe formulation of the second cross-frequency node.

This file does not assert the Navier--Stokes/PDE estimate.  It separates:

1. the real cross representation `Vcross <= x*b` with `x^2 <= Z`;
2. the analytic square-control target `b^2 <= K^2 * U^2 * Y`;
3. the algebraic construction of a nonnegative degree-two candidate from that target.

No `sup Y`, `Z / Y`, BKM/LPS endpoint, or initial-energy budget is introduced.
-/

/-- Functional cross representation required before Young absorption. -/
structure CrossRep
    (Vcross Z : ℝ → ℝ) where
  x : ℝ → ℝ
  b : ℝ → ℝ
  hx : ∀ t, x t ^ 2 ≤ Z t
  hV : ∀ t, Vcross t ≤ x t * b t

/-- Functional version of the Young-remainder factorization target.

The constant `C` must be strictly positive and the coefficient must be
pointwise nonnegative.  This is still only the T3-side factorization; no time
budget is bundled into the predicate. -/
def CrossRemainderFactorsThroughYGlobal
    (b Y : ℝ → ℝ)
    (eps : ℝ) : Prop :=
  ∃ aCross : ℝ → ℝ, ∃ C : ℝ,
    0 < C ∧
    (∀ t, 0 ≤ aCross t) ∧
    (∀ t, CrossRemainderFactorsThroughY (b t) eps C (aCross t) (Y t))

/-- Explicit candidate produced by the velocity-square route. -/
noncomputable def aCrossFromVelocity
    (K eps U : ℝ) : ℝ :=
  (K ^ 2 / (4 * eps)) * U ^ 2

/-- The explicit velocity-square candidate is nonnegative when `eps > 0`. -/
theorem aCrossFromVelocity_nonneg
    (K eps U : ℝ)
    (heps : 0 < eps) :
    0 ≤ aCrossFromVelocity K eps U := by
  unfold aCrossFromVelocity
  positivity

/-- Exact algebraic content of Node 2.

If the actual cross remainder satisfies the analytic square-control estimate

`b(t)^2 <= K^2 * U(t)^2 * Y(t)`,

then the Young remainder factors through `Y` with the explicit coefficient
`aCrossFromVelocity K eps (U t)` and constant `C = 1`.

The hypothesis `hsq` is the genuine remaining analytic/PDE-frequency node; it
is not proved here. -/
theorem cross_remainder_factors_through_Y_from_square_control
    (b U Y : ℝ → ℝ)
    (K eps : ℝ)
    (heps : 0 < eps)
    (hsq : ∀ t, CrossSquareControl (b t) K (U t) (Y t)) :
    CrossRemainderFactorsThroughYGlobal b Y eps := by
  refine ⟨fun t => aCrossFromVelocity K eps (U t), 1, by norm_num, ?_, ?_⟩
  · intro t
    exact aCrossFromVelocity_nonneg K eps (U t) heps
  · intro t
    unfold CrossRemainderFactorsThroughY
    unfold aCrossFromVelocity
    have h := hsq t
    unfold CrossSquareControl at h
    have hden : 0 < 4 * eps := by positivity
    apply (div_le_iff₀ hden).2
    calc
      b t ^ 2 ≤ K ^ 2 * U t ^ 2 * Y t := h
      _ = (1 * ((K ^ 2 / (4 * eps)) * U t ^ 2) * Y t) * (4 * eps) := by
        field_simp [ne_of_gt heps]

/-- Correct Navier--Stokes degree-two covariance of the explicit candidate.

If the velocity amplitude has degree one under the spacetime scaling
`U_lambda(t) = lambda * U(lambda^2 t)`, then the constructed cross coefficient
has degree two at the correspondingly rescaled time. -/
theorem aCrossFromVelocity_scales_degree_two
    (K eps lambda : ℝ)
    (U UScaled : ℝ → ℝ)
    (hU : ∀ t, UScaled t = lambda * U (lambda ^ 2 * t)) :
    ∀ t,
      aCrossFromVelocity K eps (UScaled t) =
        lambda ^ 2 * aCrossFromVelocity K eps (U (lambda ^ 2 * t)) := by
  intro t
  rw [hU t]
  unfold aCrossFromVelocity
  ring

/-- The exact unresolved analytic frontier after the algebraic Node-2
construction.  In particular, absence of a literal `sqrt Y` factor in a
formula for `b` is not by itself a no-go certificate; the square-control
estimate must either be proved or refuted on the actual cross representation. -/
structure CrossNode2AnalyticFrontier
    (Vcross Z Y : ℝ → ℝ) where
  rep : CrossRep Vcross Z
  U : ℝ → ℝ
  K : ℝ
  square_control : ∀ t, CrossSquareControl (rep.b t) K (U t) (Y t)
  low_velocity_degree_one : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient
