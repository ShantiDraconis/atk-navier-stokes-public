import Mathlib
import G1.G1_DynamicCriticalGeometry

noncomputable section

namespace G1Dynamic

/-!
Fail-closed hardening for N01.

This file repairs two specification defects exposed by
G1_DynamicCriticalGeometry:

1. the tangential projection formula is corrected for non-unit regularized
   directions;
2. the coherence constant is tied to a concrete Hölder inequality instead of
   an unconstrained `holds : Prop` field.

No Navier--Stokes regularity theorem is asserted.
-/

/-- Orthogonal component of F relative to a nonzero (not necessarily unit)
vector xi.  This is the algebraically correct replacement for
F - <xi,F> xi when xi is not normalized. -/
def normalizedTangentialPart (ξ F : Vec3) : Vec3 :=
  F - (((@inner ℝ Vec3 _ ξ F) / (@inner ℝ Vec3 _ ξ ξ)) : ℝ) • ξ

/-- The corrected projection is exactly orthogonal whenever the denominator is
nonzero.  This is the property that fails for the legacy non-unit formula. -/
theorem inner_normalizedTangentialPart_eq_zero
    (ξ F : Vec3)
    (hden : (@inner ℝ Vec3 _ ξ ξ) ≠ 0) :
    (@inner ℝ Vec3 _ ξ (normalizedTangentialPart ξ F)) = 0 := by
  have hcancel :
      ((@inner ℝ Vec3 _ ξ F) / (@inner ℝ Vec3 _ ξ ξ)) *
          (@inner ℝ Vec3 _ ξ ξ) =
        (@inner ℝ Vec3 _ ξ F) := by
    exact div_mul_cancel₀ _ hden
  unfold normalizedTangentialPart
  rw [inner_sub_right, inner_smul_right, hcancel]
  exact sub_self _

/-- On unit vectors the corrected formula reduces to the legacy formula. -/
theorem normalizedTangentialPart_eq_tangentialPart_of_unit
    (ξ F : Vec3)
    (hunit : (@inner ℝ Vec3 _ ξ ξ) = 1) :
    normalizedTangentialPart ξ F = tangentialPart ξ F := by
  simp [normalizedTangentialPart, tangentialPart, hunit]

/-- Concrete quantitative critical 1/2-Hölder coherence.
The constant C occurs in the inequality itself; there is no free `holds`
proposition that can be filled with True. -/
structure QuantitativeCriticalCoherenceAtTime
    (direction : Vec3 → Vec3) where
  C : ℝ
  hC : 0 ≤ C
  rho : ℝ
  hrho : 0 < rho
  region : Set Vec3
  nondegenerateRegion :
    ∃ x ∈ region, ∃ y ∈ region, x ≠ y
  holderHalf :
    ∀ ⦃x y : Vec3⦄,
      x ∈ region →
      y ∈ region →
      ‖x - y‖ < rho →
      ‖direction x - direction y‖
        ≤ C * Real.sqrt (‖x - y‖ / rho)

/-- The hardened statement exports its actual inequality rather than a Boolean
or opaque Prop payload. -/
theorem quantitative_coherence_exports_bound
    {direction : Vec3 → Vec3}
    (q : QuantitativeCriticalCoherenceAtTime direction)
    {x y : Vec3}
    (hx : x ∈ q.region)
    (hy : y ∈ q.region)
    (hxy : ‖x - y‖ < q.rho) :
    ‖direction x - direction y‖
      ≤ q.C * Real.sqrt (‖x - y‖ / q.rho) :=
  q.holderHalf hx hy hxy

/-- Quantitative kernel-side packet attached to a specific coherence witness.
The output constant must be controlled by the input coherence constant, so a
bridge cannot silently discard C as the legacy interface did.

`kernelEstimate` remains the next analytic OPEN_BRIDGE; this layer only fixes
the quantitative type contract. -/
structure QuantitativeKernelWeightedCoherence
    {direction : Vec3 → Vec3}
    (q : QuantitativeCriticalCoherenceAtTime direction) where
  kernelC : ℝ
  hkernelC : 0 ≤ kernelC
  transferFactor : ℝ
  htransferFactor : 0 ≤ transferFactor
  constantControl : kernelC ≤ transferFactor * q.C
  kernelEstimate : Prop

/-- Hardened bridge signature: the kernel packet is indexed by the exact input
coherence witness, preserving its quantitative constant. -/
structure QuantitativeCoherenceToKernelBridge
    (directionAt : ℝ → Vec3 → Vec3) where
  bridge :
    ∀ t : ℝ,
      (q : QuantitativeCriticalCoherenceAtTime (directionAt t)) →
      QuantitativeKernelWeightedCoherence q

/-- Any hardened bridge necessarily returns a packet whose constant is bounded
in terms of the actual coherence constant supplied at that time. -/
theorem hardened_bridge_preserves_constant_control
    {directionAt : ℝ → Vec3 → Vec3}
    (B : QuantitativeCoherenceToKernelBridge directionAt)
    (t : ℝ)
    (q : QuantitativeCriticalCoherenceAtTime (directionAt t)) :
    (B.bridge t q).kernelC ≤
      (B.bridge t q).transferFactor * q.C :=
  (B.bridge t q).constantControl

/-- The corrected epsilon-level tangential operator.  It is deliberately
partial at zero direction through an explicit denominator hypothesis in the
orthogonality theorem, rather than silently pretending xi_eps is unit. -/
def xiEpsTangentialPart (eps : ℝ) (ω F : Vec3) : Vec3 :=
  normalizedTangentialPart (xi_eps eps ω) F

theorem xiEpsTangentialPart_orthogonal
    (eps : ℝ) (ω F : Vec3)
    (hden : (@inner ℝ Vec3 _ (xi_eps eps ω) (xi_eps eps ω)) ≠ 0) :
    (@inner ℝ Vec3 _ (xi_eps eps ω) (xiEpsTangentialPart eps ω F)) = 0 := by
  exact inner_normalizedTangentialPart_eq_zero (xi_eps eps ω) F hden

#print axioms G1Dynamic.inner_normalizedTangentialPart_eq_zero
#print axioms G1Dynamic.normalizedTangentialPart_eq_tangentialPart_of_unit
#print axioms G1Dynamic.quantitative_coherence_exports_bound
#print axioms G1Dynamic.hardened_bridge_preserves_constant_control
#print axioms G1Dynamic.xiEpsTangentialPart_orthogonal

end G1Dynamic
