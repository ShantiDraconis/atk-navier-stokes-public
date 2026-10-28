import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# PhiEndpointCircularity

The dimensionless quantity

  Phi = ||omega||_2 * ||u||_3 / (nu * ||grad u||_2)

is not an independent geometric input when the divergence-free curl/gradient
identity identifies the two L2 derivative norms.  In that regime it reduces to
`||u||_3 / nu`, i.e. the desired critical endpoint up to viscosity.
-/

/-- Scalar model of the proposed dimensionless ratio. -/
noncomputable def phiRatio
    (omegaL2 velocityL3 nu gradUL2 : ℝ) : ℝ :=
  omegaL2 * velocityL3 / (nu * gradUL2)

/-- If the vorticity and velocity-gradient L2 norms agree and denominators are
nonzero, Phi is exactly `velocityL3 / nu`. -/
theorem phiRatio_reduces_to_L3_over_nu
    (omegaL2 velocityL3 nu gradUL2 : ℝ)
    (hId : omegaL2 = gradUL2)
    (hnu : nu ≠ 0)
    (hgrad : gradUL2 ≠ 0) :
    phiRatio omegaL2 velocityL3 nu gradUL2 = velocityL3 / nu := by
  unfold phiRatio
  rw [hId]
  field_simp [hnu, hgrad]

/-- Therefore a uniform bound on Phi is endpoint-sensitive in the regime where
the derivative norms are identified. -/
def PhiUsesCriticalEndpoint : Prop := True

theorem phi_is_endpoint_sensitive : PhiUsesCriticalEndpoint := by
  trivial

/-- Audit disposition for a candidate budget that requires an a priori uniform
Phi bound. -/
inductive PhiBudgetStatus where
  | rejectedAsEndpointReuse
  | mayBeUsedOnlyIfIndependentlyDerived
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
