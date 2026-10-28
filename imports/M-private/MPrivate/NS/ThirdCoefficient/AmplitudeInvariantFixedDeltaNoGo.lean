import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# AmplitudeInvariantFixedDeltaNoGo

A purely algebraic obstruction to the rigid route.  At a fixed spatial profile,
model nonlinear production as degree 3 in an amplitude `A` and dissipation as
degree 2.  If the geometric certificate is unchanged by amplitude scaling, it
cannot imply a universal fixed-delta estimate for every amplitude whenever the
base production is positive.

This is not a counterexample to an actual NSE trajectory.  It refutes the
algebraic implication from amplitude-invariant geometry to fixed-delta
coercivity.
-/

/-- Cubic production under amplitude scaling. -/
def amplitudeProduction (A V : ℝ) : ℝ := A^3 * V

/-- Quadratic dissipative side under amplitude scaling. -/
def amplitudeDissipation (A nu Z delta : ℝ) : ℝ :=
  (1 - delta) * nu * A^2 * Z

/-- For positive production and nonnegative dissipative coefficient, one can
choose a positive amplitude that violates the rigid depletion inequality. -/
theorem exists_amplitude_violating_fixed_delta
    (V nu Z delta : ℝ)
    (hV : 0 < V)
    (hnu : 0 ≤ nu)
    (hZ : 0 ≤ Z)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) :
    ∃ A : ℝ, 0 < A ∧
      amplitudeDissipation A nu Z delta < amplitudeProduction A V := by
  let c : ℝ := (1 - delta) * nu * Z
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  let A : ℝ := c / V + 1
  have hA : 0 < A := by
    dsimp [A]
    have hdiv : 0 ≤ c / V := div_nonneg hc (le_of_lt hV)
    linarith
  have hAV : c < A * V := by
    dsimp [A]
    have hV0 : V ≠ 0 := ne_of_gt hV
    field_simp [hV0]
    nlinarith
  refine ⟨A, hA, ?_⟩
  unfold amplitudeDissipation amplitudeProduction
  dsimp [c] at hAV ⊢
  have hA2 : 0 < A^2 := sq_pos_of_pos hA
  nlinarith

/-- Hence no hypothesis invariant under amplitude scaling can, by itself,
force the same rigid fixed-delta inequality at every amplitude for a profile
with positive production. -/
def RigidAmplitudeInvariantRouteStatus : String :=
  "FORMAL_REFUTED_AT_ALGEBRAIC_SCALING_LEVEL"

end MPrivate.NS.ThirdCoefficient
