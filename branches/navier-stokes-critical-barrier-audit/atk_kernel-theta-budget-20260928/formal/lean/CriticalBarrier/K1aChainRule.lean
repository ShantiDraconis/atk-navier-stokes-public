import Mathlib
import CriticalBarrier.K1aVectorKernel

namespace CriticalBarrier.K1aChainRule

open CriticalBarrier.K1aVectorKernel

/-- Analytic K1a chain-rule target.  This file deliberately separates the
proved algebraic kernel from the still-open Fréchet differentiability step. -/
def ChainRuleStatement (eps : ℝ) (w : ℝ → Vec3) (t : ℝ) : Prop :=
  HasDerivAt (fun s => xi eps (w s))
    (DxiCandidate eps (w t) (deriv w t)) t

/-- The exact derivative formula that must be established before the PDE lift.
It is a named target, not an assumed theorem. -/
def ExactDerivativeStatement (eps : ℝ) (w : Vec3) : Prop :=
  ∃ L : Vec3 →L[ℝ] Vec3, HasFDerivAt (xi eps) L w

/-- Fail-closed inventory: algebra is available, while analytic closure remains
an explicit proposition to be proved by a later module. -/
structure K1aAnalyticObligation where
  eps : ℝ
  heps : 0 < eps
  chainRuleClosed : Prop
  exactDerivativeClosed : Prop

end CriticalBarrier.K1aChainRule
