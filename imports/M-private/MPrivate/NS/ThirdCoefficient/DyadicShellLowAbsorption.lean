import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# DyadicShellLowAbsorption

A true reverse derivative estimate is natural on an annular/dyadic shell,
not on the entire low-pass block.  This file encodes the shellwise mechanism:

  Y_j <= gap_j^{-2} Z_j,
  V_j <= S_j Y_j,

hence

  V_j <= (S_j / gap_j^2) Z_j.

If the shell coefficient `S_j/gap_j^2` is summably/subcritically bounded, the
low block may be absorbed into dissipation.  The harmonic-analysis theorem
producing the shell estimates from actual NSE data remains open.
-/

/-- Reverse derivative control supplied by an annular spectral gap. -/
def ShellSpectralGap
    (Yj Zj gap : ℝ) : Prop :=
  0 < gap ∧ 0 ≤ Yj ∧ 0 ≤ Zj ∧ gap^2 * Yj ≤ Zj

/-- Signed shell stretching controlled by shell amplitude times shell enstrophy. -/
def ShellStretchingBound
    (Vj Sj Yj : ℝ) : Prop :=
  Vj ≤ Sj * Yj

/-- One shell absorbs with coefficient `Sj/gap^2` when `Sj>=0`. -/
theorem shell_stretching_to_dissipation
    (Vj Sj Yj Zj gap : ℝ)
    (hgap : ShellSpectralGap Yj Zj gap)
    (hS : 0 ≤ Sj)
    (hV : ShellStretchingBound Vj Sj Yj) :
    Vj ≤ (Sj / gap^2) * Zj := by
  rcases hgap with ⟨hgap0, hY, hZ, hYZ⟩
  unfold ShellStretchingBound at hV
  have hgap2 : 0 < gap^2 := sq_pos_of_pos hgap0
  have hYle : Yj ≤ Zj / gap^2 := by
    exact (le_div_iff₀ hgap2).2 (by simpa [mul_comm] using hYZ)
  have hmul := mul_le_mul_of_nonneg_left hYle hS
  calc
    Vj ≤ Sj * Yj := hV
    _ ≤ Sj * (Zj / gap^2) := hmul
    _ = (Sj / gap^2) * Zj := by field_simp [ne_of_gt hgap2]

/-- Finite shell assembly. -/
theorem finite_shell_absorption
    {ι : Type*} [Fintype ι]
    (V Z coeff : ι → ℝ)
    (eps : ℝ)
    (hV : ∀ j, V j ≤ coeff j * Z j)
    (hZ : ∀ j, 0 ≤ Z j)
    (hcoeff : ∀ j, coeff j ≤ eps) :
    ∑ j, V j ≤ eps * ∑ j, Z j := by
  calc
    ∑ j, V j ≤ ∑ j, coeff j * Z j := by
      exact Finset.sum_le_sum fun j _ => hV j
    _ ≤ ∑ j, eps * Z j := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hcoeff j) (hZ j)
    _ = eps * ∑ j, Z j := by
      rw [Finset.mul_sum]

/-- What must be proved before shellwise absorption gives `aLow=0`. -/
structure DyadicLowAbsorptionFrontier where
  actual_low_block_decomposed_into_shells : Prop
  shell_spectral_gaps : Prop
  signed_shell_stretching_bounds : Prop
  shell_coefficients_nonnegative : Prop
  shell_coefficients_uniformly_below_epsilon : Prop
  shell_dissipations_sum_below_total_Z : Prop
  no_loss_at_zero_frequency : Prop
  no_Z_div_Y : Prop
  no_endpoint_reuse : Prop

inductive DyadicLowRouteStatus where
  | algebraicReductionProved
  | analyticShellBridgeOpen
  | refutedForGivenHypotheses
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
