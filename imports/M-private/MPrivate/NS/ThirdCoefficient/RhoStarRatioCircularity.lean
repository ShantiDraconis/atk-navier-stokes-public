import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# RhoStarRatioCircularity

The coherence length

  rho_* = kappa * ||omega||_2 / ||grad omega||_2

has the correct length scaling. Its inverse square therefore has the desired
ThirdCoefficient degree +2, but algebraically it is proportional to `Z/Y`.
That makes it scale-correct but audit-forbidden as a non-circular T4 input.
-/

/-- Squared inverse coherence scale written directly in terms of enstrophy Y
and palinstrophy Z. -/
noncomputable def rhoStarInvSqFromYZ (kappa Y Z : ℝ) : ℝ :=
  Z / (kappa^2 * Y)

/-- Under `Y -> lambda Y` and `Z -> lambda^3 Z`, the ratio has degree +2. -/
theorem rhoStarInvSq_critical_scaling
    (kappa Y Z lambda : ℝ)
    (hkappa : kappa ≠ 0)
    (hY : Y ≠ 0)
    (hlambda : lambda ≠ 0) :
    rhoStarInvSqFromYZ kappa (lambda * Y) (lambda^3 * Z) =
      lambda^2 * rhoStarInvSqFromYZ kappa Y Z := by
  unfold rhoStarInvSqFromYZ
  field_simp [hkappa, hY, hlambda]

/-- Explicit marker that this construction divides by the target enstrophy. -/
def RhoStarInvSqUsesZDivY : Prop := True

theorem rhoStarInvSq_is_Z_div_Y_family :
    RhoStarInvSqUsesZDivY := by
  trivial

/-- At `Y=0`, the literal field expression is a bookkeeping convention rather
than a valid positive reciprocal scale; the degenerate branch must be proved
separately. -/
theorem rhoStarInvSq_zero_enstrophy_field_value
    (kappa Z : ℝ) :
    rhoStarInvSqFromYZ kappa 0 Z = 0 := by
  simp [rhoStarInvSqFromYZ]

/-- Audit verdict: correct scaling is insufficient for admissibility. -/
inductive RhoStarCoefficientStatus where
  | scaleCritical
  | rejectedByZDivY
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
