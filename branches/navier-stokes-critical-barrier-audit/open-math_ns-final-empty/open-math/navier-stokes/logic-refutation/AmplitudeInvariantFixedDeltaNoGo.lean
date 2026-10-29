import Mathlib

namespace NSAmplitudeInvariantNoGo

variable {State : Type}

structure ScalingModel where
  scale : ℝ → State → State
  production : State → ℝ
  dissipation : State → ℝ
  certificate : State → Prop
  production_scales :
    ∀ (A : ℝ) (u : State), 0 ≤ A →
      production (scale A u) = A^3 * production u
  dissipation_scales :
    ∀ (A : ℝ) (u : State), 0 ≤ A →
      dissipation (scale A u) = A^2 * dissipation u
  certificate_invariant :
    ∀ (A : ℝ) (u : State), 0 < A →
      (certificate (scale A u) ↔ certificate u)

def FixedDeltaDepletion
    (M : ScalingModel (State := State))
    (nu delta : ℝ) : Prop :=
  ∀ u, M.certificate u →
    M.production u ≤ (1 - delta) * nu * M.dissipation u

-- FAST_PATH_SCOPE: structural amplitude-invariance no-go; no Clay/NSE promotion.
theorem no_fixed_delta_from_amplitude_invariant_certificate
    (M : ScalingModel (State := State))
    (nu delta : ℝ)
    (hnu : 0 < nu)
    (hdelta : 0 < delta)
    (u : State)
    (hcert : M.certificate u)
    (hprod : 0 < M.production u)
    (hdiss : 0 ≤ M.dissipation u) :
    ¬ FixedDeltaDepletion M nu delta := by
  intro hfixed
  let P : ℝ := M.production u
  let C : ℝ := (1 - delta) * nu * M.dissipation u
  have hbase : P ≤ C := by
    dsimp [P, C]
    exact hfixed u hcert
  have hPpos : 0 < P := by
    simpa [P] using hprod
  have hCpos : 0 < C := lt_of_lt_of_le hPpos hbase
  let A : ℝ := C / P + 1
  have hApos : 0 < A := by
    dsimp [A]
    have hratio_nonneg : 0 ≤ C / P :=
      div_nonneg (le_of_lt hCpos) (le_of_lt hPpos)
    linarith
  have hA0 : 0 ≤ A := le_of_lt hApos
  have hInvFun :
      0 < A → (M.certificate (M.scale A u) ↔ M.certificate u) :=
    @ScalingModel.certificate_invariant State M A u
  have hInv :
      M.certificate (M.scale A u) ↔ M.certificate u :=
    hInvFun hApos
  have hcertA : M.certificate (M.scale A u) := hInv.mpr hcert
  have hProdScaleFun :
      0 ≤ A → M.production (M.scale A u) = A^3 * M.production u :=
    @ScalingModel.production_scales State M A u
  have hProdScaleA :
      M.production (M.scale A u) = A^3 * M.production u :=
    hProdScaleFun hA0
  have hDissScaleFun :
      0 ≤ A → M.dissipation (M.scale A u) = A^2 * M.dissipation u :=
    @ScalingModel.dissipation_scales State M A u
  have hDissScaleA :
      M.dissipation (M.scale A u) = A^2 * M.dissipation u :=
    hDissScaleFun hA0
  have hscaled := hfixed (M.scale A u) hcertA
  rw [hProdScaleA, hDissScaleA] at hscaled
  have htmp : C / P < A := by
    dsimp [A]
    linarith
  have hAP_gt_C : C < A * P := by
    exact (div_lt_iff₀ hPpos).mp htmp
  have hA2pos : 0 < A^2 := pow_pos hApos 2
  have hleft :
      A^2 * (A * P) ≤ A^2 * C := by
    calc
      A^2 * (A * P) = A^3 * P := by ring
      _ = A^3 * M.production u := by simp [P]
      _ ≤ (1 - delta) * nu * (A^2 * M.dissipation u) := hscaled
      _ = A^2 * C := by
        dsimp [C]
        ring
  have hright :
      A^2 * C < A^2 * (A * P) :=
    mul_lt_mul_of_pos_left hAP_gt_C hA2pos
  exact (not_lt_of_ge hleft) hright

#print axioms no_fixed_delta_from_amplitude_invariant_certificate

end NSAmplitudeInvariantNoGo
