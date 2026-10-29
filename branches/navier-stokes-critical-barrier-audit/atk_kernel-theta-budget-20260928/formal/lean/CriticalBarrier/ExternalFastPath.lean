import Mathlib
import CriticalBarrier.K1aVectorKernel
import CriticalBarrier.K1aChainRule
import CriticalBarrier.K1aPDELift
import CriticalBarrier.KernelPromotedG1Assembly
import CriticalBarrier.ScientificMeet
import CriticalBarrier.K1aClaimGate

namespace CriticalBarrier.ExternalFastPath

/-- Fail-closed five-gate compression of the scientific route.
A field is evidence, never a substitute for the theorem it names. -/
structure GateEvidence where
  statement : Prop
  proof : statement

structure K1aCoreBundle where
  exactFrechet : Prop
  chainRule : Prop
  pdeLift : Prop
  explicitRemainder : Prop

structure K1AnalyticBundle where
  cutoffFreeRemainder : Prop
  transportEstimate : Prop
  biotSavartSplit : Prop
  positiveUniformGamma : Prop
  epsilonLimit : Prop
  dimensionalNormalization : Prop

structure G1ClosureBundle where
  signedDepletion : Prop
  realProducer : Prop

structure GlobalClosureBundle where
  g2 : Prop
  g3 : Prop
  g4 : Prop
  globalRegularity : Prop

structure ExternalCertificateBundle where
  scientificMeet : Prop
  axiomAudit : Prop
  dependencyAudit : Prop
  provenanceAudit : Prop
  reproducible : Prop
  finalClaim : Prop

/-- The fast path may issue only when every compressed gate carries an
actual proof object.  This theorem is composition only; it proves no NS
analytic obligation by itself. -/
theorem compose_external
    (k1a : K1aCoreBundle)
    (k1 : K1AnalyticBundle)
    (g1 : G1ClosureBundle)
    (global : GlobalClosureBundle)
    (ext : ExternalCertificateBundle)
    (hk1a : k1a.exactFrechet ∧ k1a.chainRule ∧ k1a.pdeLift ∧ k1a.explicitRemainder)
    (hk1 : k1.cutoffFreeRemainder ∧ k1.transportEstimate ∧ k1.biotSavartSplit ∧
      k1.positiveUniformGamma ∧ k1.epsilonLimit ∧ k1.dimensionalNormalization)
    (hg1 : g1.signedDepletion ∧ g1.realProducer)
    (hglobal : global.g2 ∧ global.g3 ∧ global.g4 ∧ global.globalRegularity)
    (hext : ext.scientificMeet ∧ ext.axiomAudit ∧ ext.dependencyAudit ∧
      ext.provenanceAudit ∧ ext.reproducible ∧ ext.finalClaim) :
    ext.finalClaim :=
  hext.2.2.2.2.2

/-- Official fast-path reuse of the kernel-promoted ThirdCoefficient assembly.
    This removes duplicated algebra from the open frontier; the premises still
    must be identified with one actual Navier-Stokes solution. -/
theorem promoted_three_gate_plus_balance
    (d : KernelPromotedG1Assembly.ThreeGatePointwiseData)
    (nu yPrime : ℝ)
    (hnu : 0 < nu)
    (hT3 : KernelPromotedG1Assembly.ThreeGatePointwiseCertified d)
    (hbal : KernelPromotedG1Assembly.EnstrophyBalance yPrime nu d.Z d.V) :
    (1 / 2 : ℝ) * yPrime +
      (1 - KernelPromotedG1Assembly.pointwiseTheta d nu) * nu * d.Z ≤
      (d.C * KernelPromotedG1Assembly.pointwiseA3 d) * d.Y := by
  exact KernelPromotedG1Assembly.three_gate_plus_balance_gives_differential
    d nu yPrime hnu hT3 hbal

#print axioms CriticalBarrier.ExternalFastPath.promoted_three_gate_plus_balance

end CriticalBarrier.ExternalFastPath
