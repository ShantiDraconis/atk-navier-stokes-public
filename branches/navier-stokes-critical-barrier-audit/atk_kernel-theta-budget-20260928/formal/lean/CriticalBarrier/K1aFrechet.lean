import Mathlib
import CriticalBarrier.K1aVectorKernel
import CriticalBarrier.K1aChainRule

namespace CriticalBarrier.K1aFrechet

open CriticalBarrier.K1aVectorKernel
open CriticalBarrier.K1aChainRule

/-!
K1a exact derivative producer.

REUSE-FIRST:
* `HasFDerivAt.norm_sq`
* `HasFDerivAt.sqrt`
* `hasFDerivAt_inv`
* `HasFDerivAt.smul`
* the already frozen `DxiCLM`

No local re-proofs of these calculus primitives belong in this module.
-/

def XiFrechetTarget (eps : ℝ) (w : Vec3) : Prop :=
  HasFDerivAt (xi eps) (DxiCLM eps w) w

theorem exactDerivative_from_target
    {eps : ℝ} {w : Vec3}
    (h : XiFrechetTarget eps w) :
    ExactDerivativeStatement eps w := by
  exact ⟨DxiCLM eps w, h⟩

end CriticalBarrier.K1aFrechet
