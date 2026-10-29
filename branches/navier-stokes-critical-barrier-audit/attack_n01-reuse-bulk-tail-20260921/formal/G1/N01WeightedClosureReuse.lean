import G1.G1_DynamicCriticalGeometry_Hardened
import HypothesesComplete_v3

noncomputable section

namespace G1Dynamic

/-- Exact adapter from the current dynamic stretching data to the already
certified bulk/tail algebra layer. -/
def StretchingData.toV3 (d : StretchingData) : G1HypothesesV3.EnstrophyData where
  z := d.z
  stretch := d.stretch
  hz := d.hz

@[simp] theorem toV3_z (d : StretchingData) :
    d.toV3.z = d.z := rfl

@[simp] theorem toV3_stretch (d : StretchingData) :
    d.toV3.stretch = d.stretch := rfl

/-- The depletion predicate is definitionally the same after the adapter. -/
theorem geometricDepletion_iff_v3
    (ν : ℝ) (d : StretchingData) :
    GeometricDepletion ν d ↔
      G1HypothesesV3.GeometricDepletion ν d.toV3 := by
  rfl

/-- Forward reuse: the already-certified bulk/tail theorem discharges the
entire algebraic closure from a subcritical kernel budget to signed depletion.
The only remaining work is to derive these analytic hypotheses from ActualNS. -/
theorem bulk_tail_reuse_closes_dynamic_G1
    (ν cBulk δTail : ℝ)
    (hν : 0 ≤ ν)
    (d : StretchingData)
    (s : G1HypothesesV3.StretchSplit d.toV3)
    (hBulk : G1HypothesesV3.BulkAbsorption ν cBulk d.toV3 s)
    (hTail : G1HypothesesV3.ExceptionalTailControl ν δTail d.toV3 s)
    (hBudget : G1HypothesesV3.SubcriticalBudget cBulk δTail) :
    GeometricDepletion ν d := by
  rw [geometricDepletion_iff_v3]
  exact G1HypothesesV3.bulk_tail_to_depletion
    ν cBulk δTail hν d.toV3 s hBulk hTail hBudget

/-- Therefore a kernel estimate need only produce the three analytic
premises consumed above; no second depletion proof is required. -/
structure KernelBudgetCertificate
    (ν : ℝ) (d : StretchingData) where
  split : G1HypothesesV3.StretchSplit d.toV3
  cBulk : ℝ
  δTail : ℝ
  bulk : G1HypothesesV3.BulkAbsorption ν cBulk d.toV3 split
  tail : G1HypothesesV3.ExceptionalTailControl ν δTail d.toV3 split
  budget : G1HypothesesV3.SubcriticalBudget cBulk δTail

theorem kernelBudgetCertificate_closes
    (ν : ℝ) (hν : 0 ≤ ν)
    (d : StretchingData)
    (K : KernelBudgetCertificate ν d) :
    GeometricDepletion ν d :=
  bulk_tail_reuse_closes_dynamic_G1
    ν K.cBulk K.δTail hν d K.split K.bulk K.tail K.budget

#print axioms G1Dynamic.geometricDepletion_iff_v3
#print axioms G1Dynamic.bulk_tail_reuse_closes_dynamic_G1
#print axioms G1Dynamic.kernelBudgetCertificate_closes

end G1Dynamic
