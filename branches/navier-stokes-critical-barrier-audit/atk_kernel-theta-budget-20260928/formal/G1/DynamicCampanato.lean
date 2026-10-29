/-
DynamicCampanato.lean

Audit-level interface for the PDE -> dynamic Campanato bridge, keeping the
local-energy identity exact and non-circular.

Design rules match the rest of `formal/G1`:
* no `axiom`
* no `sorry`
* no `True` endpoint placeholders
* every analytic gap is recorded as an explicit `Prop` field
* `R1`, `R2`, and the cutoff-free remainder witness stay visible
* `FinalF.lean` is not touched here
* FAIL-PROOF: LocalEnergyIdentityData/ofXiEpsPDE are conditional on supplied
  XiEpsPDE Prop fields; they are not counted as derivations from the PDE
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import G1.XiEpsPDE

noncomputable section G1DynamicCampanatoSection

namespace G1DynamicCampanato

abbrev Cutoff := G1XiEpsPDE.Cutoff
abbrev rhoStar := G1XiEpsPDE.rhoStar
abbrev rhoStarFixed := G1XiEpsPDE.rhoStarFixed

open G1XiEpsPDE

/-- The Campanato exponent forced by the linear `r / ρ_*` error term. -/
def betaCampanato : ℝ := 1

lemma betaCampanato_eq : betaCampanato = 1 := rfl

/-- The fixed cutoff radius is exactly `R = K ρ_*`. -/
theorem w_R_radius_formula
    {κ K omegaL2 gradOmegaL2 : ℝ}
    (w : Cutoff κ K omegaL2 gradOmegaL2) :
    w.R = K * rhoStar κ omegaL2 gradOmegaL2 := by
  simpa [rhoStarFixed, rhoStar] using w.hR

/--
Conditional local-energy bookkeeping copied from an `XiEpsPDE` record and its
supplied identity field.  This is not, by itself, a derivation of the PDE test.

Intended analytic interpretation: testing `XiEpsPDE` against
`φ² (ξ_ε - (ξ_ε)_{B_r}) |ω|_ε` with `φ = w_R` and `R = K ρ_*`.

This structure records the identity term-by-term, without absorbing `R1`, `R2`,
or the remainder into a cubic ratio such as `‖∇ω‖₂³ / ‖ω‖₂`.
-/
structure LocalEnergyIdentityData where
  xiPDE : XiEpsPDE
  kappa : ℝ
  K : ℝ
  omegaL2 : ℝ
  gradOmegaL2 : ℝ
  r : ℝ
  hr : 0 < r
  cutoff : Cutoff kappa K omegaL2 gradOmegaL2
  temporal : ℝ
  transport : ℝ
  stretchNear : ℝ
  stretchFar : ℝ
  diffusionMain : ℝ
  crossCutoffOrderOne : ℝ
  crossCutoffOrderTwo : ℝ
  crossGradMag : ℝ
  drift : ℝ
  R1Term : ℝ
  R2Term : ℝ
  /-- Exact test choice: `φ² (ξ_ε - (ξ_ε)_{B_r}) |ω|_ε` with `φ = w_R`. -/
  tests_XiEpsPDE_exactly : Prop
  /-- Exact identity with no hidden absorption. -/
  identity :
    temporal =
      transport + stretchNear + stretchFar + diffusionMain
        + crossCutoffOrderOne + crossCutoffOrderTwo + crossGradMag
        + drift + R1Term + R2Term
  /-- `C_rem(‖u₀‖₂, ν)` remains explicit and cutoff-free. -/
  remainder_cutoff_free :
    (xiPDE.remainderWitness.C_rem =
      xiPDE.remainderWitness.dependencyModel
        xiPDE.remainderWitness.u0L2 xiPDE.remainderWitness.nu) ∧
    0 < xiPDE.remainderWitness.C_rem
  /-- No replacement by `‖∇ω‖₂³ / ‖ω‖₂` occurs at this stage:
      retain the exact R1/R2 representation carried by XiEpsPDE. -/
  no_cubic_ratio_reduction :
    (∀ x, xiPDE.R1 x =
      G1XiEpsPDE.regularizedChainMap
        (G1XiEpsPDE.magEps xiPDE.ω_ε xiPDE.ε x)
        (G1XiEpsPDE.xiEps xiPDE.ω_ε xiPDE.ε x)
        (xiPDE.R1_numerator x)) ∧
    (∀ x, xiPDE.R2 x =
      ((xiPDE.ε ^ 2) / (G1XiEpsPDE.magEps xiPDE.ω_ε xiPDE.ε x) ^ 3) • xiPDE.gradOmega x)

def LocalEnergyIdentityData.ofXiEpsPDE
    (h : XiEpsPDE)
    {kappa K omegaL2 gradOmegaL2 r : ℝ}
    (hr : 0 < r)
    (φ : Cutoff kappa K omegaL2 gradOmegaL2) :
    LocalEnergyIdentityData where
  xiPDE := h
  kappa := kappa
  K := K
  omegaL2 := omegaL2
  gradOmegaL2 := gradOmegaL2
  r := r
  hr := hr
  cutoff := φ
  temporal := h.temporal
  transport := h.transport
  stretchNear := h.stretchNear
  stretchFar := h.stretchFar
  diffusionMain := h.diffusionMain
  crossCutoffOrderOne := h.crossCutoffOrderOne
  crossCutoffOrderTwo := h.crossCutoffOrderTwo
  crossGradMag := h.crossGradMag
  drift := h.drift
  R1Term := h.R1Term
  R2Term := h.R2Term
  tests_XiEpsPDE_exactly := h.local_energy_test
  identity := h.local_energy_identity
  remainder_cutoff_free := ⟨h.remainderWitness.independence_certificate, h.remainderWitness.hC_rem_pos⟩
  no_cubic_ratio_reduction := ⟨by intro x; rfl, h.R2_definition⟩

/-- "PROVED_IDENTITY" means only that the arithmetic identity stored in
LocalEnergyIdentityData is available.  It does not certify that the identity
was analytically derived from Navier–Stokes. -/
def PROVED_IDENTITY (I : LocalEnergyIdentityData) : Prop :=
  I.temporal =
    I.transport + I.stretchNear + I.stretchFar + I.diffusionMain
      + I.crossCutoffOrderOne + I.crossCutoffOrderTwo + I.crossGradMag
      + I.drift + I.R1Term + I.R2Term

theorem ofXiEpsPDE_PROVED_IDENTITY
    (h : XiEpsPDE)
    {kappa K omegaL2 gradOmegaL2 r : ℝ}
    (hr : 0 < r)
    (φ : Cutoff kappa K omegaL2 gradOmegaL2) :
    PROVED_IDENTITY (LocalEnergyIdentityData.ofXiEpsPDE h hr φ) := by
  exact (LocalEnergyIdentityData.ofXiEpsPDE h hr φ).identity

/-- FAIL-PROOF: a valid cutoff for a trivial parameter choice. -/
def vacuousCutoff : Cutoff 1 1 1 1 where
  hgrad := by norm_num
  R := 1
  hR := by
    norm_num [G1XiEpsPDE.rhoStarFixed, G1XiEpsPDE.rhoStar]
  hR_pos := by norm_num

/-- FAIL-PROOF: the vacuous XiEpsPDE specification from XiEpsPDE.lean
propagates through `ofXiEpsPDE` and yields `PROVED_IDENTITY`.  Therefore
this theorem is conditional bookkeeping, not a PDE derivation certificate. -/
def vacuousLocalEnergyIdentityData : LocalEnergyIdentityData :=
  LocalEnergyIdentityData.ofXiEpsPDE
    G1XiEpsPDE.vacuousXiEpsPDESpec
    (kappa := 1) (K := 1) (omegaL2 := 1) (gradOmegaL2 := 1) (r := 1)
    (by norm_num) vacuousCutoff

theorem proved_identity_interface_accepts_vacuous_pde :
    PROVED_IDENTITY vacuousLocalEnergyIdentityData := by
  exact vacuousLocalEnergyIdentityData.identity

theorem localEnergy_radius_formula (I : LocalEnergyIdentityData) :
    I.cutoff.R = I.K * rhoStar I.kappa I.omegaL2 I.gradOmegaL2 :=
  w_R_radius_formula I.cutoff

/--
Correctly scaled far-field control: only the averaged form is allowed.

The factor `(r / ρ_*)^β` is fixed here with `β = 1`, i.e. the scale that matches
the linear error term in the Campanato step and does not introduce `ρ_*^{-2}`.
-/
structure FarFieldAveragedBound where
  C_far : ℝ
  rhoStar : ℝ
  r : ℝ
  omegaL2 : ℝ
  farFieldSqAvg : ℝ
  hC_far : 0 ≤ C_far
  hr : 0 ≤ r
  hr_le_rhoStar : r ≤ rhoStar
  hrhoStar : 0 < rhoStar
  homegaL2 : 0 ≤ omegaL2
  estimate :
    farFieldSqAvg ≤
      C_far * (omegaL2 ^ 2 / rhoStar ^ 3) *
        Real.rpow (r / rhoStar) betaCampanato
  /-- OPEN_CZ: the signed cancellation needed to derive the gain is still open. -/
  OPEN_CZ : Prop

theorem farField_linear_ratio (F : FarFieldAveragedBound) :
    F.farFieldSqAvg ≤
      F.C_far * (F.omegaL2 ^ 2 / F.rhoStar ^ 3) * (F.r / F.rhoStar) := by
  simpa [betaCampanato, Real.rpow_one] using F.estimate

/--
With `β = 1`, the far-field factor is bounded by `1` whenever `0 ≤ r ≤ ρ_*`.
This is the compatibility needed to stay within the Leray energy budget rather
than introducing a palinstrophy-level `ρ_*^{-2}` coefficient.
-/
theorem betaCampanato_energy_only
    {A r rho : ℝ}
    (hA : 0 ≤ A)
    (hr : 0 ≤ r)
    (hr_le_rho : r ≤ rho)
    (hrho : 0 < rho) :
    A * Real.rpow (r / rho) betaCampanato ≤ A := by
  have hratio_le_one : r / rho ≤ 1 := by
    exact (div_le_iff₀ hrho).2 (by simpa using hr_le_rho)
  have hmul : A * (r / rho) ≤ A * 1 :=
    mul_le_mul_of_nonneg_left hratio_le_one hA
  simpa [betaCampanato, Real.rpow_one] using hmul

/-- One step of the Campanato iteration `J_{r/2} ≤ γ J_r + A r / ρ_*`. -/
structure CampanatoIterationStep where
  gamma : ℝ
  A : ℝ
  rhoStar : ℝ
  r : ℝ
  Jr : ℝ
  Jhalf : ℝ
  hgamma : 0 ≤ gamma
  hA : 0 ≤ A
  hr : 0 ≤ r
  hrhoStar : 0 < rhoStar
  step : Jhalf ≤ gamma * Jr + A * (r / rhoStar)

theorem iterate_linear_barrier
    (S : CampanatoIterationStep)
    {C : ℝ}
    (hJr : S.Jr ≤ C * (S.r / S.rhoStar)) :
    S.Jhalf ≤ (S.gamma * C + S.A) * (S.r / S.rhoStar) := by
  have hmul :
      S.gamma * S.Jr ≤ S.gamma * (C * (S.r / S.rhoStar)) :=
    mul_le_mul_of_nonneg_left hJr S.hgamma
  have hbase :
      S.Jhalf ≤ S.gamma * (C * (S.r / S.rhoStar)) + S.A * (S.r / S.rhoStar) := by
    linarith [S.step, hmul]
  have hfactor :
      S.gamma * (C * (S.r / S.rhoStar)) + S.A * (S.r / S.rhoStar) =
        (S.gamma * C + S.A) * (S.r / S.rhoStar) := by
    ring
  rw [hfactor] at hbase
  exact hbase

theorem iterate_to_half_scale
    (S : CampanatoIterationStep)
    {C : ℝ}
    (hJr : S.Jr ≤ C * (S.r / S.rhoStar))
    (hpreserve : 2 * S.gamma * C + 2 * S.A ≤ C) :
    S.Jhalf ≤ C * ((S.r / 2) / S.rhoStar) := by
  have hratio_nonneg : 0 ≤ S.r / S.rhoStar := by
    exact div_nonneg S.hr S.hrhoStar.le
  have hlin :
      S.Jhalf ≤ (S.gamma * C + S.A) * (S.r / S.rhoStar) :=
    iterate_linear_barrier S hJr
  have hcoeff : S.gamma * C + S.A ≤ C / 2 := by
    linarith
  have hmul :
      (S.gamma * C + S.A) * (S.r / S.rhoStar) ≤
        (C / 2) * (S.r / S.rhoStar) :=
    mul_le_mul_of_nonneg_right hcoeff hratio_nonneg
  have hrewrite :
      (C / 2) * (S.r / S.rhoStar) = C * ((S.r / 2) / S.rhoStar) := by
    ring
  calc
    S.Jhalf ≤ (S.gamma * C + S.A) * (S.r / S.rhoStar) := hlin
    _ ≤ (C / 2) * (S.r / S.rhoStar) := hmul
    _ = C * ((S.r / 2) / S.rhoStar) := hrewrite

/--
If the linear barrier is preserved with a nonzero inhomogeneous error, then the
contraction coefficient must satisfy `γ < 1/2`.
-/
theorem gamma_lt_half_of_barrier_condition
    {gamma A C : ℝ}
    (hC : 0 < C)
    (hA : 0 < A)
    (hpreserve : 2 * gamma * C + 2 * A ≤ C) :
    gamma < (1 : ℝ) / 2 := by
  have hstrict : 2 * gamma * C < C := by
    linarith
  have hmul : gamma * (2 * C) < C := by
    nlinarith
  have h2C : 0 < 2 * C := by
    positivity
  have hgamma : gamma < C / (2 * C) :=
    (lt_div_iff₀ h2C).2 hmul
  have hfrac : C / (2 * C) = (1 : ℝ) / 2 := by
    field_simp [hC.ne']
    <;> ring
  simpa [hfrac] using hgamma

/--
The diffusion side must supply a genuine half-contraction after choosing `κ`;
recording merely `γ < 1` is insufficient for the Campanato barrier.
-/
structure DiffusionHalfContraction where
  kappa : ℝ
  gammaDiff : ℝ
  hkappa : 0 < kappa
  half_contraction : gammaDiff ≤ (1 : ℝ) / 2
  produced_by_diffusion : Prop

/-- Signed far-field formulation left open until the cancellation gain is proved. -/
structure StretchFarSignedOpenCZ where
  rhoStar : ℝ
  r : ℝ
  betaMissing : ℝ
  hr : 0 ≤ r
  hrhoStar : 0 < rhoStar
  hbetaMissing : 0 < betaMissing
  signed_form : Prop
  OPEN_CZ : Prop

/-- Consolidated non-circular PDE -> dynamic Campanato interface. -/
structure PDEToDynamicCampanatoBridge where
  localEnergy : LocalEnergyIdentityData
  farField : FarFieldAveragedBound
  stretchFarSigned : StretchFarSignedOpenCZ
  diffusionChoice : DiffusionHalfContraction
  iteration : CampanatoIterationStep
  /-- OPEN_BRIDGE: the near-field gain must come from the PDE identity itself,
      not by importing `hDynamic` as an input hypothesis. -/
  no_hDynamic_circularity : Prop

end G1DynamicCampanato

end G1DynamicCampanatoSection
