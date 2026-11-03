import CriticalBarrier.GlobalRegularityFromG1

/-!
# Navier-Stokes OPEN_MATH CORE

Fail-closed reduction of the Navier-Stokes G1 producer to one mathematical core:
a uniform strict signed-depletion estimate derived from ActualNS.

This file does not assert that estimate. It proves that, once that single core
statement is supplied, the already-closed G1Bridge can be inhabited with zero
defect, so defect integrability is no longer an independent gap.
-/

namespace CriticalBarrier.OpenMath.NavierStokes

open CriticalBarrier.GlobalRegularityFromG1

variable {State : Type}

/-- Physical time-dependent data needed by the already-certified G1 interface. -/
structure PhysicalStretchingData where
  y : State → ℝ → ℝ
  z : State → ℝ → ℝ
  stretching : State → ℝ → ℝ
  nu : ℝ
  y_nonneg : ∀ u t, 0 ≤ y u t
  z_nonneg : ∀ u t, 0 ≤ z u t
  nu_pos : 0 < nu

/-- The exact remaining mathematical producer.

The same positive delta must work for every ActualNS state and every time.
No L3 endpoint, G1Bridge, or global regularity is assumed. -/
structure StrictSignedDepletionProducer
    (ActualNS : State → Prop)
    (D : PhysicalStretchingData (State := State)) where
  delta : ℝ
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  depletion :
    ∀ u, ActualNS u → ∀ t,
      D.stretching u t ≤ (1 - delta) * D.nu * D.z u t

/-- A strict signed-depletion producer mechanically yields the existing G1Bridge
with zero lower-order defect. This closes the bookkeeping/integrability side. -/
def StrictSignedDepletionProducer.toG1Bridge
    {ActualNS : State → Prop}
    {D : PhysicalStretchingData (State := State)}
    (h : StrictSignedDepletionProducer ActualNS D) :
    G1Bridge ActualNS where
  defect := fun _ _ => 0
  stretchingData := fun u t =>
    { y := D.y u t
      z := D.z u t
      stretching := D.stretching u t
      nu := D.nu
      theta := 1 - h.delta
      a := 0
      y_nonneg := D.y_nonneg u t
      z_nonneg := D.z_nonneg u t
      nu_pos := D.nu_pos
      theta_nonneg := by linarith [h.delta_le_one]
      theta_lt_one := by linarith [h.delta_pos] }
  actual_to_signed := by
    intro u hu t
    dsimp [SignedDepletionAt]
    have hd := h.depletion u hu t
    simpa using hd
  defect_integrable := by
    intro u hu
    simpa using (integrable_zero : Integrable (fun _ : ℝ => (0 : ℝ)))

/-- The isolated one-gap OPEN_MATH statement. -/
def NSOpenMathCore
    (ActualNS : State → Prop)
    (D : PhysicalStretchingData (State := State)) : Prop :=
  Nonempty (StrictSignedDepletionProducer ActualNS D)

/-- Once the single OPEN_MATH core is inhabited, all G1 bookkeeping is closed. -/
theorem g1Bridge_of_openMathCore
    {ActualNS : State → Prop}
    {D : PhysicalStretchingData (State := State)}
    (h : NSOpenMathCore ActualNS D) :
    Nonempty (G1Bridge ActualNS) := by
  rcases h with ⟨hp⟩
  exact ⟨hp.toG1Bridge⟩

end CriticalBarrier.OpenMath.NavierStokes
