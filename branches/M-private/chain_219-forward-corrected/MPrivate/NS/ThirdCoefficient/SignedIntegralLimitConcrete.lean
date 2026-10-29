import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace MPrivate.NS.ThirdCoefficient

open Filter MeasureTheory

variable {α : Type*} [MeasurableSpace α]

theorem integral_upper_bound_of_dominated_signed_truncations
    (μ : Measure α)
    (F : ℕ → α → ℝ)
    (f bound : α → ℝ)
    (B : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound_integrable : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x)))
    (hupper : ∀ n, (∫ x, F n x ∂μ) ≤ B) :
    (∫ x, f x ∂μ) ≤ B := by
  have hconv :
      Tendsto (fun n => ∫ x, F n x ∂μ) atTop (nhds (∫ x, f x ∂μ)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hF hbound_integrable hbound hlim
  exact le_of_tendsto' hconv hupper

theorem concrete_signed_limit_preserves_cross_energy_gain
    (μ : Measure α)
    (F : ℕ → α → ℝ)
    (aCross g bound : α → ℝ)
    (Cstar : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound_integrable : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (aCross x)))
    (hupper : ∀ n, (∫ x, F n x ∂μ) ≤ Cstar * (∫ x, g x ∂μ)) :
    (∫ x, aCross x ∂μ) ≤ Cstar * (∫ x, g x ∂μ) := by
  exact integral_upper_bound_of_dominated_signed_truncations
    μ F aCross bound (Cstar * (∫ x, g x ∂μ))
    hF hbound_integrable hbound hlim hupper

end MPrivate.NS.ThirdCoefficient
