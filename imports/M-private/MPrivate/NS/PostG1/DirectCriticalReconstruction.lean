import Mathlib

namespace MPrivate.NS.PostG1

/-!
# DirectCriticalReconstruction

If G1-flex yields a uniform enstrophy/gradient bound, a separate LP high/low
reconstruction is not logically necessary. The classical scalar route is

  ||u||_3^2 <= ||u||_2 ||u||_6
  ||u||_6 <= C ||grad u||_2

combined with energy control of `||u||_2` and vorticity/gradient control.

This file certifies only the scalar algebra once the actual analytic norm
identifications and inequalities are supplied.  It does not prove homogeneous
Sobolev, interpolation, Helmholtz identities, or the endpoint `L∞_t L^3_x`
mapping for Navier--Stokes.
-/

/-- Scalar abstraction of interpolation and Sobolev inputs. -/
def InterpolationSobolevData
    (L3 U2 U6 C gradU2 : ℝ) : Prop :=
  0 ≤ U2 ∧ 0 ≤ U6 ∧ 0 ≤ C ∧ 0 ≤ gradU2 ∧
  L3^2 ≤ U2 * U6 ∧
  U6 ≤ C * gradU2

/-- Interpolation plus Sobolev gives a squared critical bound. -/
theorem interpolation_sobolev_to_squared_L3
    (L3 U2 U6 C gradU2 : ℝ)
    (h : InterpolationSobolevData L3 U2 U6 C gradU2) :
    L3^2 ≤ C * U2 * gradU2 := by
  rcases h with ⟨hU2, hU6, hC, hG, hinterp, hsob⟩
  have hprod : U2 * U6 ≤ U2 * (C * gradU2) :=
    mul_le_mul_of_nonneg_left hsob hU2
  calc
    L3^2 ≤ U2 * U6 := hinterp
    _ ≤ U2 * (C * gradU2) := hprod
    _ = C * U2 * gradU2 := by ac_rfl

/-- Adding uniform energy and gradient bounds yields a uniform squared L3 bound. -/
theorem energy_enstrophy_to_uniform_squared_L3
    (L3 U2 U6 C gradU2 E M : ℝ)
    (h : InterpolationSobolevData L3 U2 U6 C gradU2)
    (hE : U2 ≤ E)
    (hM : gradU2 ≤ M)
    (hE0 : 0 ≤ E)
    (hM0 : 0 ≤ M) :
    L3^2 ≤ C * E * M := by
  rcases h with ⟨hU2, hU6, hC, hG, hinterp, hsob⟩
  have hbase : L3^2 ≤ C * U2 * gradU2 := by
    apply interpolation_sobolev_to_squared_L3 L3 U2 U6 C gradU2
    exact ⟨hU2, hU6, hC, hG, hinterp, hsob⟩
  have h1 : C * U2 * gradU2 ≤ C * E * gradU2 := by
    have hCE : C * U2 ≤ C * E := mul_le_mul_of_nonneg_left hE hC
    exact mul_le_mul_of_nonneg_right hCE hG
  have h2 : C * E * gradU2 ≤ C * E * M := by
    exact mul_le_mul_of_nonneg_left hM (mul_nonneg hC hE0)
  exact hbase.trans (h1.trans h2)

/-- The direct route still needs the analytic identification/control of actual
Navier--Stokes norms in the exact solution class. -/
structure DirectCriticalReconstructionFrontier where
  actual_solution_norms_identified : Prop
  domain_is_pinned : Prop
  solution_class_is_pinned : Prop
  interpolation_L2_L6_to_L3 : Prop
  homogeneous_sobolev_L6_from_grad : Prop
  homogeneous_sobolev_applicable_to_solution : Prop
  divergence_free : Prop
  grad_u_controlled_by_vorticity : Prop
  grad_vorticity_identity_or_bound_domain_valid : Prop
  energy_uniform_L2 : Prop
  G1_uniform_enstrophy : Prop
  constants_uniform_in_time : Prop
  squared_L3_bound_converted_to_L3_bound : Prop
  pointwise_time_bound_mapped_to_essential_supremum : Prop
  maximal_interval_uniformity : Prop
  critical_space_exactly_L3 : Prop
  no_endpoint_reuse : Prop
  uniform_L3_conclusion : Prop

inductive DirectReconstructionStatus where
  | conditional
  | proved
  deriving DecidableEq, Repr

end MPrivate.NS.PostG1
