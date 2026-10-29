import Mathlib
import CriticalBarrier.K1aVectorKernel
import CriticalBarrier.K1aChainRule
import CriticalBarrier.K1aExactFrechetProducer

namespace CriticalBarrier.K1aPDELift

open CriticalBarrier.K1aVectorKernel
open CriticalBarrier.K1aChainRule

/-- Pointwise material vorticity equation D_t omega = S omega + nu Delta omega.
The fields are data; no Navier-Stokes solution is fabricated here. -/
structure VorticityMaterialData where
  eps : ℝ
  heps : 0 < eps
  nu : ℝ
  hnu : 0 < nu
  omega : Vec3
  materialOmega : Vec3
  strainOmega : Vec3
  laplacianOmega : Vec3
  vorticityEquation :
    materialOmega = strainOmega + nu • laplacianOmega

/-- Exact regularized-direction PDE target obtained by applying the K1a
derivative operator to the vorticity material equation. -/
def XiMaterialTarget (d : VorticityMaterialData) : Prop :=
  DxiCandidate d.eps d.omega d.materialOmega =
    DxiCandidate d.eps d.omega d.strainOmega +
      d.nu • DxiCandidate d.eps d.omega d.laplacianOmega

/-- Algebraic linearity in the derivative direction is the next kernel lemma
needed for the PDE lift. -/
def DxiLinearityTarget (eps : ℝ) (w : Vec3) : Prop :=
  (∀ a b : Vec3,
    DxiCandidate eps w (a + b) =
      DxiCandidate eps w a + DxiCandidate eps w b) ∧
  (∀ (c : ℝ) (a : Vec3),
    DxiCandidate eps w (c • a) =
      c • DxiCandidate eps w a)

theorem DxiLinearityTarget_closed (eps : ℝ) (w : Vec3) :
    DxiLinearityTarget eps w := by
  constructor
  · exact DxiCandidate_add eps w
  · intro c a
    exact DxiCandidate_smul eps c w a

/-- The pointwise PDE lift is already forced by the frozen linearity lemmas;
no new analytic hypothesis is needed for this algebraic step. -/
theorem XiMaterialTarget_closed (d : VorticityMaterialData) :
    XiMaterialTarget d := by
  unfold XiMaterialTarget
  rw [d.vorticityEquation]
  rw [DxiCandidate_add]
  rw [DxiCandidate_smul]

/-- Fail-closed K1a PDE-lift package.  Analytic chain rule and algebraic
linearity must both be discharged before XiMaterialTarget is promotable. -/
structure PDELiftObligation (d : VorticityMaterialData) where
  exactDerivative : ExactDerivativeStatement d.eps d.omega
  linearity : DxiLinearityTarget d.eps d.omega
  xiMaterial : XiMaterialTarget d

/-- Forward composition: the exact derivative producer plus the already-closed
    linearity and material identities inhabit the full K1a PDE-lift obligation. -/
def PDELiftObligation_closed (d : VorticityMaterialData) :
    PDELiftObligation d where
  exactDerivative :=
    CriticalBarrier.K1aExactFrechetProducer.exactDerivativeStatement_closed
      d.heps d.omega
  linearity := DxiLinearityTarget_closed d.eps d.omega
  xiMaterial := XiMaterialTarget_closed d

#print axioms CriticalBarrier.K1aPDELift.PDELiftObligation_closed

end CriticalBarrier.K1aPDELift
