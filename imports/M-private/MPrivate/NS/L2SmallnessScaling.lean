import Mathlib

namespace MPrivate.NS

/-- Abstract `L²` kinetic-energy scaling under Navier--Stokes dilation:
    `E₀[u_λ] = λ⁻¹ E₀[u]`. -/
noncomputable def scaledInitialEnergy (E₀ lambda : ℝ) : ℝ := E₀ / lambda

/-- Any fixed nonnegative energy can be made smaller than an arbitrary positive
    threshold by taking a sufficiently large scale parameter.  This is only a
    scaling statement; it proves no regularity or blow-up conclusion. -/
theorem l2_energy_can_be_scaled_below_any_positive_threshold
    {E₀ δ : ℝ}
    (hE : 0 ≤ E₀)
    (hδ : 0 < δ) :
    ∃ lambda : ℝ, 0 < lambda ∧ scaledInitialEnergy E₀ lambda < δ := by
  let lambda : ℝ := E₀ / δ + 1
  have hratio : 0 ≤ E₀ / δ := div_nonneg hE hδ.le
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    linarith
  refine ⟨lambda, hlambda, ?_⟩
  unfold scaledInitialEnergy
  apply (div_lt_iff₀ hlambda).2
  dsimp [lambda]
  field_simp [ne_of_gt hδ]
  nlinarith

end MPrivate.NS
