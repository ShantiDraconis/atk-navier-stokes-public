import Mathlib

namespace NSEnergyCompressionBarrier

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

def EnergyOnlyControl
    (Admissible : State → Prop)
    (energyProjection : State → EnergyData)
    (criticalResidual : State → ℝ) : Prop :=
  ∃ F : EnergyData → ℝ,
    ∀ u : State,
      Admissible u →
      criticalResidual u ≤ F (energyProjection u)

theorem fiber_unbounded_implies_no_energy_only_control
    (Admissible : State → Prop)
    (energyProjection : State → EnergyData)
    (criticalResidual : State → ℝ)
    (h : CriticalUnboundedOnFiber Admissible energyProjection criticalResidual) :
    ¬ EnergyOnlyControl Admissible energyProjection criticalResidual := by
  intro hControl
  rcases hControl with ⟨F, hF⟩
  rcases h with ⟨e, he⟩
  rcases he (F e) with ⟨u, hu, hπ, hgt⟩
  have hle := hF u hu
  rw [hπ] at hle
  linarith

def EnergyOnlyFactorization
    (Admissible : State → Prop)
    (energyProjection : State → EnergyData)
    (criticalResidual : State → ℝ) : Prop :=
  ∃ F : EnergyData → ℝ,
    ∀ u : State,
      Admissible u →
      criticalResidual u = F (energyProjection u)

theorem fiber_unbounded_implies_no_factorization
    (Admissible : State → Prop)
    (energyProjection : State → EnergyData)
    (criticalResidual : State → ℝ)
    (h : CriticalUnboundedOnFiber Admissible energyProjection criticalResidual) :
    ¬ EnergyOnlyFactorization Admissible energyProjection criticalResidual := by
  intro hFactor
  rcases hFactor with ⟨F, hF⟩
  have hControl : EnergyOnlyControl Admissible energyProjection criticalResidual := by
    refine ⟨F, ?_⟩
    intro u hu
    rw [hF u hu]
  exact (fiber_unbounded_implies_no_energy_only_control
    Admissible energyProjection criticalResidual h) hControl

#print axioms fiber_unbounded_implies_no_energy_only_control
#print axioms fiber_unbounded_implies_no_factorization

end NSEnergyCompressionBarrier
