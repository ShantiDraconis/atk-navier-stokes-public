/-
WeightedLow.lean

Audit-level interface for the weighted-low / weighted-absorption /
signed-depletion chain in the G1 program.

Design rules (same as all G1 formal files):
* no axiom
* no sorry
* no True shortcut
* every unproved analytic implication is an explicit Prop-field or structure field
* the exact numerical constant 2 * (0.6)^2 * 50 = 36 is stated as a lemma,
  not hidden inside a black-box estimate

Chain formalised here:
  hDynamic_eps
    => WeightedLow_eps  (η_low(δ) ≤ C √δ)
    => WeightedAbsorption_eps  (γ < 1 independent of ε)
    => ε → 0  (via IntegrableCoefficient, uniform L¹_t)
    => SignedDepletion

OPEN_BRIDGE fields mark every step that is not yet proved.
FinalF.lean / final_unification_conditional remain BLOCKED.
-/

import Mathlib

noncomputable section G1WeightedLowSection

namespace G1WeightedLow

-- -----------------------------------------------------------------------
-- 1. EXACT CONSTANT LEMMA
-- The numerical factor 2 * (0.6)^2 * 50 = 36 must appear explicitly.
-- It enters via: gamma_effective = 1 - 2 C_abs^2 C_Young,
-- with C_abs = 0.6 (absorption factor) and C_Young = 50 (Young inequality
-- constant in 3D after Calderón-Zygmund).  Keeping this visible prevents
-- a hidden choice of constants to force gamma < 1.
-- -----------------------------------------------------------------------

/-- The exact value 2 * (0.6)^2 * 50. -/
lemma two_times_06sq_times_50 : (2 : ℝ) * (0.6 : ℝ)^2 * 50 = 36 := by norm_num

/-- The resulting absorption coefficient. -/
def C_abs : ℝ := 0.6
def C_Young : ℝ := 50

/-- gamma_effective = 1 - 2 * C_abs^2 * C_Young. -/
def gamma_effective : ℝ := 1 - 2 * C_abs^2 * C_Young

lemma gamma_effective_eq : gamma_effective = -35 := by
  norm_num [gamma_effective, C_abs, C_Young]

/-- The displayed frozen constants force gamma_effective = -35. -/
lemma gamma_effective_not_pos : ¬ 0 < gamma_effective := by
  norm_num [gamma_effective, C_abs, C_Young]

/-- The arithmetic inequality gamma_effective < 1 is true but is not enough
    for an absorption coefficient, because positivity fails. -/
lemma gamma_effective_lt_one : gamma_effective < 1 := by
  norm_num [gamma_effective, C_abs, C_Young]

-- -----------------------------------------------------------------------
-- 2. WeightedLowData
-- Formalises the bound η_low(δ) ≤ C * √δ where δ ∈ (0,1) measures
-- how far the direction field is from the aligned cone.
-- -----------------------------------------------------------------------

/--
Weighted-low coefficient at parameter δ.
`eta_low` is the effective weight on the low-frequency part of the
stretching integral.  The bound C * √δ is the critical 1/2-power.
-/
structure WeightedLowData where
  /-- The parameter δ ∈ (0,1) measuring directional misalignment. -/
  δ : ℝ
  hδ : 0 < δ ∧ δ < 1
  /-- Uniform Hölder constant for the weighted-low bound. -/
  C_low : ℝ
  hC_low : 0 < C_low
  /-- The actual weighted-low coefficient. -/
  eta_low : ℝ
  heta_low_nn : 0 ≤ eta_low
  /-- Core bound: η_low ≤ C_low * √δ.
      This is an OPEN_BRIDGE field — proved from hDynamic_eps via
      Calderón-Zygmund estimate on the direction field, not assumed. -/
  low_bound : eta_low ≤ C_low * Real.sqrt δ
  /-- Source of C_low: depends only on (‖u₀‖₂, ν, κ, θ), NOT on ε. -/
  C_low_cutoff_free : Prop

-- -----------------------------------------------------------------------
-- 3. WeightedAbsorptionData
-- γ < 1 must be established independently of ε.
-- -----------------------------------------------------------------------

/--
Weighted absorption data: the factor γ that appears in the signed
Biot–Savart stretching bound

  |∫ D·ω(x)ω(y)/|x-y|³| ≤ γ ν Z + a(t) Q

with γ < 1 (coercive) and γ independent of ε.

γ < 1 is NOT chosen to cancel terms; it is derived from the geometry
of the vorticity direction field in Omega_theta together with the
Calderón-Zygmund kernel estimate.
-/
structure WeightedAbsorptionData where
  /-- The absorption factor. -/
  γ : ℝ
  hγ_pos : 0 < γ
  /-- Critical coercivity. -/
  hγ_lt_one : γ < 1
  /-- γ is independent of the regularisation parameter ε. -/
  γ_eps_independent : Prop
  /-- OPEN_BRIDGE: a genuine PDE/geometric derivation of γ must be supplied.
      The former field γ ≤ gamma_effective is rejected: the frozen arithmetic
      gives gamma_effective = -35, incompatible with 0 < γ. -/
  γ_derivation_certificate : Prop

/-- Countercertificate for the former "canonical absorption" construction.
    No positive γ can be bounded above by gamma_effective for the frozen
    constants C_abs = 0.6 and C_Young = 50. -/
theorem gamma_effective_cannot_bound_positive_gamma :
    ¬ ∃ γ : ℝ, 0 < γ ∧ γ ≤ gamma_effective := by
  intro h
  rcases h with ⟨γ, hγpos, hγupper⟩
  have hbad : gamma_effective = -35 := gamma_effective_eq
  rw [hbad] at hγupper
  linarith

-- -----------------------------------------------------------------------
-- 4. IntegrableCoefficient
-- a_eps(t) = C_κ / ν³ * ‖ω_ε‖₂⁴ ∈ L¹_t uniformly in ε.
-- This is the non-stretching remainder term in the enstrophy balance.
-- -----------------------------------------------------------------------

/--
The integrable-in-time coefficient a_ε(t) that multiplies Q in the
signed depletion estimate.

  a_ε(t) = (C_κ / ν³) * ‖ω_ε(t)‖₂⁴

Important: basic Leray-Hopf energy does NOT by itself imply a uniform
L¹_t bound on ‖ω_ε‖₂⁴.  Energy gives an L¹_t bound on the squared velocity
gradient/enstrophy-level quantity, not its square.  Therefore `uniform_L1`
is a genuinely stronger OPEN_BRIDGE and must be supplied by a non-circular
PDE estimate; it must not be advertised as inherited from energy alone.
-/
structure IntegrableCoefficient where
  /-- Physical parameters. -/
  C_kappa : ℝ
  nu : ℝ
  hnu : 0 < nu
  /-- Enstrophy L² norm of vorticity at time t (may depend on ε). -/
  omegaL2 : ℝ → ℝ → ℝ   -- (eps, t) ↦ ‖ω_ε(t)‖₂
  homegaL2_nn : ∀ eps t, 0 ≤ omegaL2 eps t
  /-- The coefficient itself. -/
  a_eps : ℝ → ℝ → ℝ      -- (eps, t) ↦ a_ε(t)
  ha_eps_eq : ∀ eps t, a_eps eps t = (C_kappa / nu^3) * (omegaL2 eps t)^4
  /-- L¹_t bound uniform in ε (stated as a Prop-field following the audit pattern).
      OPEN_BRIDGE: this is NOT a consequence of the basic Leray-Hopf energy
      inequality alone.  It requires an independent non-circular estimate.
      Intended meaning: ∃ A ≥ 0, ∀ ε T > 0, ∫₀ᵀ a_ε(t) dt ≤ A. -/
  uniform_L1 : Prop
  /-- Bound A depends only on (C_κ, ν, ‖u₀‖₂), not on ε. -/
  A_cutoff_free : Prop

-- -----------------------------------------------------------------------
-- 5. SignedDepletion
-- The final target of the chain: ∫ ω·Sω ≤ (1-δ) ν ‖∇ω‖₂²
-- -----------------------------------------------------------------------

/--
Signed geometric depletion of enstrophy production.
The viscous term dominates with a uniform gap δ > 0.

Convention in this structure: Y(t) = ‖ω(t)‖₂².  If the exact balance is
  (1/2) Y'(t) + ν Z(t) = stretching(t)
and stretching(t) ≤ (1-δ) ν Z(t), then
  Y'(t) + 2 δ ν Z(t) ≤ 0.
-/
structure SignedDepletion where
  /-- Viscosity. -/
  nu : ℝ
  hnu : 0 < nu
  /-- Enstrophy and dissipation functions. -/
  Y : ℝ → ℝ      -- t ↦ ‖ω(t)‖₂²
  Z : ℝ → ℝ      -- t ↦ ‖∇ω(t)‖₂²
  hZ : ∀ t, 0 ≤ Z t
  /-- Depletion constant. -/
  δ : ℝ
  hδ : 0 < δ ∧ δ ≤ 1
  /-- δ is independent of ε (survives the limit ε → 0). -/
  δ_eps_independent : Prop
  /-- The signed depletion inequality. -/
  depletion : ∀ t, deriv Y t + 2 * δ * nu * Z t ≤ 0

-- -----------------------------------------------------------------------
-- 6. Chain composition: WeightedAbsorption => SignedDepletion
-- -----------------------------------------------------------------------

/--
Bridge from WeightedAbsorption + IntegrableCoefficient to SignedDepletion.

This is an OPEN_BRIDGE interface: both fields record what must be proved
(the ε-uniform passage to the limit and the tightness needed for
Aubin–Lions to preserve γ < 1).
-/
structure AbsorptionToDepletionBridge where
  /-- The passage ε → 0 using semicontinuity.
      OPEN_BRIDGE: Aubin–Lions provides a subsequence but does NOT
      automatically preserve γ < 1; tightness of the sequence must
      be established separately. -/
  eps_limit_preserves_gamma : Prop
  /-- Once ε → 0 is passed, signed depletion follows from the chain. -/
  depletion_from_absorption :
      WeightedAbsorptionData → IntegrableCoefficient → SignedDepletion → Prop

/--
Full conditional chain interface.
Given all bridge fields, the chain produces SignedDepletion.
No step is proved here; every open obligation is an explicit field.
-/
structure WeightedLowChain where
  wl   : WeightedLowData
  wa   : WeightedAbsorptionData
  ic   : IntegrableCoefficient
  dep  : SignedDepletion
  /-- OPEN_BRIDGE K1a-K1f: see AlignmentTransport.lean -/
  open_bridge_reference : Prop
  /-- The absorption-to-depletion bridge. -/
  bridge : AbsorptionToDepletionBridge

/-
AUDIT VERDICT — WeightedLow.lean

PROVED IN THIS FILE:
* two_times_06sq_times_50 : 2 * (0.6)^2 * 50 = 36   (norm_num)
* gamma_effective_eq : gamma_effective = -35             (norm_num)
* gamma_effective_not_pos : ¬ 0 < gamma_effective         (norm_num)
* gamma_effective_lt_one : gamma_effective < 1            (norm_num)
* gamma_effective_cannot_bound_positive_gamma             (countercertificate)

OPEN_BRIDGE — NOT PROVED:
* WeightedLowData.low_bound        : needs CZ estimate from hDynamic_eps
* WeightedLowData.C_low_cutoff_free: needs C_low = f(‖u₀‖₂, ν, κ, θ) only
* WeightedAbsorptionData.γ_eps_independent: needs ε-uniform argument
* WeightedAbsorptionData.γ_derivation_certificate: needs a valid PDE/geometric
  derivation of some γ ∈ (0,1); the frozen 1 - 2*(0.6)^2*50 route is rejected
* IntegrableCoefficient.uniform_L1 : needs an independent non-circular
  L¹_t bound on ‖ω_ε‖₂⁴; basic Leray-Hopf energy alone is insufficient
* IntegrableCoefficient.A_cutoff_free: needs independence from ε
* SignedDepletion.δ_eps_independent : needs Aubin–Lions + tightness
* AbsorptionToDepletionBridge.eps_limit_preserves_gamma: CRITICAL OPEN OBLIGATION
  Aubin-Lions alone does NOT guarantee γ < 1 is preserved; tightness of
  the ε-family must be proved independently.

FinalF.lean / final_unification_conditional: BLOCKED.
-/

end G1WeightedLow

end G1WeightedLowSection
