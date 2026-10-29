import Mathlib

namespace NSFiberUnboundedFromScaling

variable {State EnergyData : Type}

def CriticalUnboundedOnFiber
    (Admissible : State → Prop)
    (energyProjection : State → EnergyData)
    (criticalResidual : State → ℝ) : Prop :=
  ∃ e : EnergyData,
    ∀ M : ℝ,
      ∃ u : State,
        Admissible u ∧
        energyProjection u = e ∧
        M < criticalResidual u

structure ScalingWitness
    (Admissible : State → Prop)
    (energyProjection : State → EnergyData)
    (criticalResidual : State → ℝ) where
  baseEnergy : EnergyData
  family : ℝ → State
  residualSlope : ℝ
  slope_pos : 0 < residualSlope
  admissible : ∀ t : ℝ, 0 ≤ t → Admissible (family t)
  fixed_energy : ∀ t : ℝ, 0 ≤ t → energyProjection (family t) = baseEnergy
  residual_lower :
    ∀ t : ℝ, 0 ≤ t →
      t * residualSlope ≤ criticalResidual (family t)

theorem scaling_witness_implies_fiber_unbounded
    (Admissible : State → Prop)
    (energyProjection : State → EnergyData)
    (criticalResidual : State → ℝ)
    (W : ScalingWitness Admissible energyProjection criticalResidual) :
    CriticalUnboundedOnFiber Admissible energyProjection criticalResidual := by
  refine ⟨W.baseEnergy, ?_⟩
  intro M
  let t : ℝ := max 0 ((M + 1) / W.residualSlope)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact le_max_left _ _
  have hspos : 0 < W.residualSlope := W.slope_pos
  have hdiv :
      M + 1 ≤ t * W.residualSlope := by
    have hle : (M + 1) / W.residualSlope ≤ t := by
      dsimp [t]
      exact le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hspos)
    have hsne : W.residualSlope ≠ 0 := ne_of_gt hspos
    have heq :
        ((M + 1) / W.residualSlope) * W.residualSlope = M + 1 := by
      field_simp [hsne]
    rw [heq] at hmul
    exact hmul
  have hM : M < t * W.residualSlope := by
    linarith
  refine ⟨W.family t, W.admissible t ht0, W.fixed_energy t ht0, ?_⟩
  exact lt_of_lt_of_le hM (W.residual_lower t ht0)

#print axioms scaling_witness_implies_fiber_unbounded

end NSFiberUnboundedFromScaling
