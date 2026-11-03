/-
XiEpsPDE.lean

Audit-level specification for the ε-regularised direction equation used in
the PDE -> dynamic Campanato bridge.

FAIL-PROOF STATUS:
* the regularisation definitions below are concrete;
* `equation` is no longer an unconstrained Prop field: it is a typed
  pointwise equality between explicit vector-field channels;
* the radial diffusion channel is now computed from explicit scalar gradient
  data rather than supplied as an arbitrary vector field;
* the tangential strain channel is computed from ξ_ε, and `strainXi` is
  linked componentwise to the matrix action `S_ε ξ_ε`;
* the remaining typed channels, scalar gradient data, and the identification
  of `S_ε` itself with the symmetric velocity gradient still require
  derivation from the Navier--Stokes vorticity equation;
* the historical R2 channel is now correctly matrix-valued and is no longer
  inserted into the vector-valued ξ_ε evolution equation;
* the raw commutator channel is now passed through the exact regularized
  chain-rule map before entering the ξ_ε equation;
* a corrected PDE derivation must still identify the raw commutator numerator,
  diffusion channels, and scalar gradient data from Navier--Stokes.

This file fixes the regularisation conventions:
* `|ω|_ε = sqrt(|ω|² + ε²) ≥ ε`
* `ξ_ε = ω / |ω|_ε`
* `R1` is the chain-rule corrected image of `[J_ε, u · ∇] ω`
* historical/proposed `R2 = ε² ∇ω_ε / |ω|_ε³` is retained as a
  matrix-valued derivative candidate for audit, not as a vector PDE forcing term;
* the cutoff-free remainder witness `C_rem(‖u₀‖₂, ν)` stays explicit
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section G1XiEpsPDESection

namespace G1XiEpsPDE

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)
abbrev ScalarField := Vec3 → ℝ
abbrev VectorField := Vec3 → Vec3
abbrev MatrixField := Vec3 → Matrix (Fin 3) (Fin 3) ℝ

/-- Scale-covariant coherence radius `ρ_* = κ ‖ω‖₂ / ‖∇ω‖₂`. -/
def rhoStar (κ omegaL2 gradOmegaL2 : ℝ) : ℝ :=
  κ * omegaL2 / gradOmegaL2

/-- Fixed cutoff radius `R = K ρ_*`. -/
def rhoStarFixed (κ K omegaL2 gradOmegaL2 : ℝ) : ℝ :=
  K * rhoStar κ omegaL2 gradOmegaL2

/-- Cutoff-free witness for the remainder constant `C_rem(‖u₀‖₂, ν)`. -/
structure RemainderCutoffFreeWitness where
  u0L2 : ℝ
  nu : ℝ
  C_rem : ℝ
  hC_rem_pos : 0 < C_rem
  dependencyModel : ℝ → ℝ → ℝ
  /-- Concrete cutoff-free dependency statement: `C_rem` is determined only by
      `‖u₀‖₂` and `ν`. -/
  independence_certificate : C_rem = dependencyModel u0L2 nu

/-- Window data with `R = K ρ_*`. -/
structure Cutoff (κ K omegaL2 gradOmegaL2 : ℝ) where
  hgrad : 0 < gradOmegaL2
  R : ℝ
  hR : R = rhoStarFixed κ K omegaL2 gradOmegaL2
  hR_pos : 0 < R

/-- `|ω|_ε = sqrt(|ω|² + ε²)`. -/
def magEps (ω : VectorField) (ε : ℝ) (x : Vec3) : ℝ :=
  Real.sqrt (‖ω x‖ ^ 2 + ε ^ 2)

/-- `ξ_ε = ω / |ω|_ε`, written as scalar multiplication by `|ω|_ε⁻¹`. -/
def xiEps (ω : VectorField) (ε : ℝ) (x : Vec3) : Vec3 :=
  (magEps ω ε x)⁻¹ • ω x

/-- Algebraic chain-rule map associated with the regularized normalization.
For r > 0 and ξ = ω/r, the differential of ω ↦ ω/r acts on a variation v
through this form after the derivative of r is substituted.  It is NOT named
an orthogonal projection because ξ need not be unit for ε > 0. -/
def regularizedChainMap (r : ℝ) (ξ v : Vec3) : Vec3 :=
  r⁻¹ • (v - ((@inner ℝ Vec3 _ ξ v)) • ξ)

theorem regularizedChainMap_unfold (r : ℝ) (ξ v : Vec3) :
    regularizedChainMap r ξ v =
      r⁻¹ • (v - ((@inner ℝ Vec3 _ ξ v)) • ξ) := rfl

/-- Chain-rule corrected commutator/forcing channel for the normalized field. -/
def commutatorCorrectionTerm
    (ω : VectorField) (ε : ℝ) (raw : VectorField) : VectorField :=
  fun x =>
    regularizedChainMap (magEps ω ε x) (xiEps ω ε x) (raw x)

/--
Typed pointwise form of the regularised direction equation.

This definition deliberately separates the *shape* of the PDE from the
analytic derivation of its channels.  Unlike a bare `Prop`, callers cannot
replace the equation by `True`; they must provide vector fields satisfying the
displayed equality.
-/
def XiEpsEquation
    (nu : ℝ)
    (materialDerivativeXi strainTangential diffusionLaplacian
      diffusionDrift radialDiffusion R1 : VectorField) : Prop :=
  ∀ x,
    materialDerivativeXi x =
      strainTangential x +
        nu • (diffusionLaplacian x + diffusionDrift x + radialDiffusion x) +
        R1 x

/--
Concrete radial diffusion channel predicted by differentiating
`ξ_ε = ω / r_ε`, with `r_ε = sqrt(|ω|² + ε²)`.

The scalar inputs stand for `|∇ω|²` and `|∇r_ε|²`; tying those inputs to
actual derivatives is the next OPEN_BRIDGE.
-/
def radialDiffusionTerm
    (ω : VectorField) (ε : ℝ)
    (gradOmegaSq gradMagSq : ScalarField) : VectorField :=
  fun x =>
    ((gradOmegaSq x - gradMagSq x) / (magEps ω ε x) ^ 2) •
      xiEps ω ε x

/-- Tangential strain channel
`Sξ - <ξ,Sξ> ξ`, computed from the supplied strain action `Sξ`. -/
def tangentialStrainTerm
    (ω : VectorField) (ε : ℝ) (strainXi : VectorField) : VectorField :=
  fun x =>
    strainXi x -
      ((@inner ℝ Vec3 _ (xiEps ω ε x) (strainXi x))) • xiEps ω ε x

structure XiEpsPDE where
  ε : ℝ
  hε : 0 < ε
  ω_ε : VectorField
  u_ε : VectorField
  /-- Symmetric strain matrix field `S_ε = sym ∇u_ε`. -/
  S_ε : MatrixField
  remainderWitness : RemainderCutoffFreeWitness
  /-- Raw commutator/forcing numerator representing `[J_ε, u · ∇] ω`.
      Its contribution to the ξ_ε equation is computed by
      `commutatorCorrectionTerm`, not supplied as a free vector field. -/
  R1_numerator : VectorField
  /-- Spatial Jacobian/gradient data for the vorticity field. -/
  gradOmega : MatrixField
  /-- Historical derivative-level R2 candidate.  This is matrix-valued because
      `∇ω` is a Jacobian; it is therefore NOT inserted as a vector term in the
      ξ_ε evolution equation. -/
  R2 : MatrixField
  R2_definition :
    ∀ x, R2 x = ((ε ^ 2) / (magEps ω_ε ε x) ^ 3) • gradOmega x
  /-- Explicit `L¹_t L¹_x` vanishing scale for `R1`. -/
  R1_L1_bound : ℝ
  /-- `R1 → 0` with cutoff-free `C_rem(‖u₀‖₂, ν)`. -/
  hR1_vanishes : R1_L1_bound ≤ remainderWitness.C_rem * ε
  /-- Componentwise bound for the matrix-valued historical R2 candidate.
      We do not manufacture a matrix norm instance merely to state this audit
      obligation. -/
  hR2_bound :
    ∀ x i j, |R2 x i j| ≤
      remainderWitness.C_rem * (ε / magEps ω_ε ε x)
  /-- Typed material derivative channel `D_t ξ_ε`. -/
  materialDerivativeXi : VectorField
  /-- Strain action `S_ε ξ_ε`. -/
  strainXi : VectorField
  /-- Componentwise identification of the supplied strain action with the
      matrix field `S_ε` applied to the regularised direction.  This avoids
      hiding a Matrix/EuclideanSpace coercion in the audit layer. -/
  strainXi_definition :
    ∀ x i, strainXi x i =
      ∑ j : Fin 3, S_ε x i j * xiEps ω_ε ε x j
  /-- Typed Laplacian channel `Δξ_ε`. -/
  diffusionLaplacian : VectorField
  /-- Typed drift channel corresponding to the gradient-of-magnitude term. -/
  diffusionDrift : VectorField
  /-- Scalar field intended to be `|∇ω_ε|²`. -/
  gradOmegaSq : ScalarField
  /-- Scalar field intended to be `|∇r_ε|²`, where
      `r_ε = sqrt(|ω_ε|² + ε²)`. -/
  gradMagSq : ScalarField
  /-- Kernel-checkable pointwise PDE equality.  The radial channel is no
      longer free: it is computed by `radialDiffusionTerm`. -/
  equation_proof :
    XiEpsEquation remainderWitness.nu materialDerivativeXi
      (tangentialStrainTerm ω_ε ε strainXi)
      diffusionLaplacian diffusionDrift
      (radialDiffusionTerm ω_ε ε gradOmegaSq gradMagSq)
      (commutatorCorrectionTerm ω_ε ε R1_numerator)
  /-- OPEN_SPECIFICATION: exact test identity must be derived from the
      corrected concrete PDE, not merely supplied as an arbitrary Prop. -/
  local_energy_test : Prop
  /-- Scalar bookkeeping terms for the tested identity. -/
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
  /-- Exact identity produced by the PDE test. -/
  local_energy_identity :
    temporal =
      transport + stretchNear + stretchFar + diffusionMain
        + crossCutoffOrderOne + crossCutoffOrderTwo + crossGradMag
        + drift + R1Term + R2Term

/-- Chain-rule corrected commutator contribution derived from the raw numerator. -/
def XiEpsPDE.R1 (h : XiEpsPDE) : VectorField :=
  commutatorCorrectionTerm h.ω_ε h.ε h.R1_numerator

/-- Radial diffusion channel determined by the scalar gradient data. -/
def XiEpsPDE.radialDiffusion (h : XiEpsPDE) : VectorField :=
  radialDiffusionTerm h.ω_ε h.ε h.gradOmegaSq h.gradMagSq

/-- Tangential strain channel determined by ξ_ε and the supplied Sξ action. -/
def XiEpsPDE.strainTangential (h : XiEpsPDE) : VectorField :=
  tangentialStrainTerm h.ω_ε h.ε h.strainXi

/-- Public equation proposition reconstructed from the typed channels. -/
def XiEpsPDE.equation (h : XiEpsPDE) : Prop :=
  XiEpsEquation h.remainderWitness.nu h.materialDerivativeXi h.strainTangential
    h.diffusionLaplacian h.diffusionDrift h.radialDiffusion h.R1

/-- Every XiEpsPDE record carries a proof of its typed pointwise equation. -/
theorem XiEpsPDE.equation_holds (h : XiEpsPDE) : h.equation := by
  exact h.equation_proof

theorem xiEps_unfold
    (ω : VectorField) (ε : ℝ) (x : Vec3) :
    xiEps ω ε x = (magEps ω ε x)⁻¹ • ω x := rfl

theorem magEps_unfold
    (ω : VectorField) (ε : ℝ) (x : Vec3) :
    magEps ω ε x = Real.sqrt (‖ω x‖ ^ 2 + ε ^ 2) := rfl

/-- A proof-status countercertificate for the *remaining* gap: even after
replacing the arbitrary equation Prop by a typed vector-field equality, the
record can still be inhabited by zero channels.  Therefore the typed equation
fixes the specification layer but does not yet derive the channels from the
Navier--Stokes vorticity equation. -/
def zeroVectorField : VectorField := fun _ => 0

def zeroMatrixField : MatrixField := fun _ => 0

def trivialRemainderWitness : RemainderCutoffFreeWitness where
  u0L2 := 0
  nu := 1
  C_rem := 1
  hC_rem_pos := by norm_num
  dependencyModel := fun _ _ => 1
  independence_certificate := rfl

def vacuousXiEpsPDESpec : XiEpsPDE where
  ε := 1
  hε := by norm_num
  ω_ε := zeroVectorField
  u_ε := zeroVectorField
  S_ε := zeroMatrixField
  remainderWitness := trivialRemainderWitness
  R1_numerator := zeroVectorField
  gradOmega := zeroMatrixField
  R2 := zeroMatrixField
  R2_definition := by
    intro x
    simp [zeroMatrixField, magEps]
  R1_L1_bound := 0
  hR1_vanishes := by
    norm_num [trivialRemainderWitness]
  hR2_bound := by
    intro x i j
    simp [zeroMatrixField, magEps, trivialRemainderWitness]
  materialDerivativeXi := zeroVectorField
  strainXi := zeroVectorField
  strainXi_definition := by
    intro x i
    simp [zeroVectorField, zeroMatrixField, xiEps, magEps]
  diffusionLaplacian := zeroVectorField
  diffusionDrift := zeroVectorField
  gradOmegaSq := fun _ => 0
  gradMagSq := fun _ => 0
  equation_proof := by
    intro x
    simp [XiEpsEquation, tangentialStrainTerm, radialDiffusionTerm,
      commutatorCorrectionTerm, regularizedChainMap,
      zeroVectorField, xiEps, magEps, trivialRemainderWitness]
  local_energy_test := True
  temporal := 0
  transport := 0
  stretchNear := 0
  stretchFar := 0
  diffusionMain := 0
  crossCutoffOrderOne := 0
  crossCutoffOrderTwo := 0
  crossGradMag := 0
  drift := 0
  R1Term := 0
  R2Term := 0
  local_energy_identity := by norm_num

theorem xieps_record_allows_vacuous_equation :
    vacuousXiEpsPDESpec.equation := by
  exact vacuousXiEpsPDESpec.equation_proof

theorem xieps_record_allows_vacuous_local_energy_test :
    vacuousXiEpsPDESpec.local_energy_test := by
  trivial

end G1XiEpsPDE

end G1XiEpsPDESection
