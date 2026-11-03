import CriticalBarrier.OpenMath.NavierStokes.OpenMathCore
import CriticalBarrier.OpenMath.NavierStokes.G1ProducerFastPath

namespace CriticalBarrier.OpenMath.NavierStokes

variable {State : Type}

/-- Reuse adapter: the already-existing G1 fast-path data are exactly the
strict-depletion data needed by the canonical OpenMathCore, modulo the
irrelevant enstrophy field `y`. No PDE content is added here. -/
def physicalDataOfG1Data
    (D : NSG1ProducerFastPath.Data (State := State))
    (y : State → ℝ → ℝ)
    (hy : ∀ u t, 0 ≤ y u t) :
    PhysicalStretchingData (State := State) where
  y := y
  z := D.dissipation
  stretching := D.stretching
  nu := D.nu
  y_nonneg := hy
  z_nonneg := D.hdissipation
  nu_pos := D.hnu

/-- Existing uniform G1Producer directly inhabits the canonical
StrictSignedDepletionProducer. -/
def strictProducerOfG1Producer
    (ActualNS : State → Prop)
    (D : NSG1ProducerFastPath.Data (State := State))
    (y : State → ℝ → ℝ)
    (hy : ∀ u t, 0 ≤ y u t)
    (P : NSG1ProducerFastPath.G1Producer ActualNS D) :
    StrictSignedDepletionProducer ActualNS (physicalDataOfG1Data D y hy) where
  delta := P.delta
  delta_pos := P.delta_pos
  delta_le_one := P.delta_le_one
  depletion := P.signed

/-- Therefore the already-existing G1 producer contract is sufficient for the
canonical one-gap NSOpenMathCore. -/
theorem g1Producer_implies_openMathCore
    (ActualNS : State → Prop)
    (D : NSG1ProducerFastPath.Data (State := State))
    (y : State → ℝ → ℝ)
    (hy : ∀ u t, 0 ≤ y u t)
    (P : NSG1ProducerFastPath.G1Producer ActualNS D) :
    NSOpenMathCore ActualNS (physicalDataOfG1Data D y hy) := by
  exact ⟨strictProducerOfG1Producer ActualNS D y hy P⟩

/-- Existing bulk/tail producer is therefore a sufficient upstream witness for
the canonical OpenMathCore, with the algebraic bulk/tail proof reused from
G1ProducerFastPath. -/
theorem bulkTail_implies_openMathCore
    (ActualNS : State → Prop)
    (D : NSG1ProducerFastPath.Data (State := State))
    (y : State → ℝ → ℝ)
    (hy : ∀ u t, 0 ≤ y u t)
    (B : NSG1ProducerFastPath.BulkTailProducer ActualNS D) :
    NSOpenMathCore ActualNS (physicalDataOfG1Data D y hy) := by
  exact g1Producer_implies_openMathCore ActualNS D y hy
    (NSG1ProducerFastPath.bulkTail_to_G1Producer ActualNS D B)

#print axioms strictProducerOfG1Producer
#print axioms g1Producer_implies_openMathCore
#print axioms bulkTail_implies_openMathCore

end CriticalBarrier.OpenMath.NavierStokes
