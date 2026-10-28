import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-- Abstract no-go theorem behind the `‖S‖₃²` budget obstruction.

`A` represents the scale-invariant time integral `∫ ‖S‖₃² dt`.
`E` represents the initial `L²` kinetic energy, which scales like `λ⁻¹ E`.

If `A > 0`, no positive universal constant can satisfy
`A ≤ C (λ⁻¹ E)` for every `λ > 0`. -/
theorem no_uniform_scaleInvariant_budget_from_L2_energy
    {A E C : ℝ}
    (hA : 0 < A)
    (hE : 0 ≤ E)
    (hC : 0 < C)
    (hbudget : ∀ lambda : ℝ, 0 < lambda → A ≤ C * E / lambda) : False := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  let lambda : ℝ := C * E / A + 1
  have hratio : 0 ≤ C * E / A := by
    exact div_nonneg (mul_nonneg hC.le hE) hA.le
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    linarith
  have hbound : A ≤ C * E / lambda := hbudget lambda hlambda
  have hstrict : C * E / lambda < A := by
    apply (div_lt_iff₀ hlambda).2
    dsimp [lambda]
    field_simp [hA0]
    nlinarith
  exact (not_lt_of_ge hbound) hstrict

/-- Negated-existence form used by the ledger. -/
theorem no_positive_universal_constant_for_L2_budget
    {A E : ℝ}
    (hA : 0 < A)
    (hE : 0 ≤ E) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 0 < lambda → A ≤ C * E / lambda := by
  rintro ⟨C, hC, hbudget⟩
  exact no_uniform_scaleInvariant_budget_from_L2_energy hA hE hC hbudget

/-- General functional version.  Instead of assuming continuity of `F` at zero,
    the theorem asks for exactly the smallness property needed by the scaling
    argument.  This avoids smuggling an analytic limit theorem into the certificate. -/
theorem no_budget_of_scaling_to_arbitrarily_small_values
    {A E : ℝ} (F : ℝ → ℝ)
    (hA : 0 < A)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ lambda : ℝ, 0 < lambda ∧ F (E / lambda) < δ)
    (hbudget : ∀ lambda : ℝ, 0 < lambda → A ≤ F (E / lambda)) : False := by
  obtain ⟨lambda, hlambda, hF⟩ := hsmall A hA
  have hA_le := hbudget lambda hlambda
  exact (not_lt_of_ge hA_le) hF

end MPrivate.NS.ThirdCoefficient
