import Mathlib

namespace G1WeightedLowConstantFirewall

/-- The constants currently written in formal/G1/WeightedLow.lean. -/
def C_abs : ℝ := 0.6
def C_Young : ℝ := 50
def gamma_effective : ℝ := 1 - 2 * C_abs^2 * C_Young

theorem gamma_effective_eq_neg35 :
    gamma_effective = -35 := by
  norm_num [gamma_effective, C_abs, C_Young]

theorem gamma_effective_not_positive :
    ¬ (0 < gamma_effective) := by
  rw [gamma_effective_eq_neg35]
  norm_num

theorem no_positive_gamma_below_gamma_effective :
    ¬ ∃ γ : ℝ, 0 < γ ∧ γ ≤ gamma_effective := by
  rintro ⟨γ, hγpos, hγle⟩
  rw [gamma_effective_eq_neg35] at hγle
  linarith

/--
Firewall for the current numerical choice:
a positive absorption coefficient cannot simultaneously satisfy
γ ≤ 1 - 2*(0.6)^2*50.
Therefore this concrete constant package cannot instantiate the
positive/subcritical absorption producer.
-/
theorem current_constant_package_cannot_close_absorption :
    ∀ γ : ℝ,
      0 < γ →
      ¬ (γ ≤ gamma_effective) := by
  intro γ hγ hle
  exact no_positive_gamma_below_gamma_effective ⟨γ, hγ, hle⟩

#print axioms G1WeightedLowConstantFirewall.gamma_effective_eq_neg35
#print axioms G1WeightedLowConstantFirewall.gamma_effective_not_positive
#print axioms G1WeightedLowConstantFirewall.no_positive_gamma_below_gamma_effective
#print axioms G1WeightedLowConstantFirewall.current_constant_package_cannot_close_absorption

end G1WeightedLowConstantFirewall
