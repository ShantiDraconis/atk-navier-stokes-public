import open_math.ActualNSToSignedGainCore.P1_ConcretePDE

/-!
NS-FORCING-001 / zero-solution material sanity check.

This file contains no sorry/admit/axiom.  It validates the concrete PDE
observables and the exact bulk/tail/remainder target on the zero solution.
-/


noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSProducerFirst.P1Concrete

/-- The zero velocity/pressure pair is a concrete smooth NSE state for zero
forcing, at every viscosity and on every time set. -/
def zeroState (times : Set ℝ) (ν : ℝ) :
    SmoothNSState times ν (fun _ => 0) where
  velocity := fun _ => 0
  pressure := fun _ => 0
  velocity_smooth := contDiff_const.contDiffOn
  pressure_smooth := contDiff_const.contDiffOn
  satisfies_nse := by
    constructor
    · intro t ht x
      simp [spatialDivergence, spatialDerivative]
    · intro t ht x
      simp [navierStokesResidual, temporalDerivative, advection,
        spatialLaplacian, spatialDerivative, pressureGradient]

@[simp] theorem vorticity_zero (t : ℝ) (x : Space) :
    vorticity (fun _ => 0) t x = 0 := by
  simp [vorticity, spatialDerivative, curlLinear, derivativeEntry]

@[simp] theorem enstrophy_zero (t : ℝ) :
    enstrophy (fun _ => 0) t = 0 := by
  simp [enstrophy, enstrophyDensity]

@[simp] theorem palinstrophy_zero (t : ℝ) :
    palinstrophy (fun _ => 0) t = 0 := by
  simp [palinstrophy, palinstrophyDensity]

@[simp] theorem stretching_zero (t : ℝ) :
    stretching (fun _ => 0) t = 0 := by
  simp [stretching, stretchingDensity]

/-- Exact material tuple for the zero concrete NSE state.

This is the same existential shape as P1_concrete_material_attempt, with
all three pieces and all three constants chosen to be zero.
-/
theorem zero_material_witness
    (times : Set ℝ) (ν : ℝ) :
    ∃ (bulk tail remainder : ℝ → ℝ)
      (cBulk cTail C : ℝ),
      0 ≤ cBulk ∧
      0 ≤ cTail ∧
      cBulk + cTail < 1 ∧
      (∀ t,
        stretching (zeroState times ν).velocity t =
          bulk t + tail t + remainder t) ∧
      (∀ t,
        bulk t ≤ cBulk * ν * palinstrophy (zeroState times ν).velocity t) ∧
      (∀ t,
        tail t ≤ cTail * ν * palinstrophy (zeroState times ν).velocity t) ∧
      (∀ t,
        remainder t ≤ C * (enstrophy (zeroState times ν).velocity t)^2) := by
  refine ⟨(fun _ => 0), (fun _ => 0), (fun _ => 0), 0, 0, 0, ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · intro t
    simp [zeroState]
  constructor
  · intro t
    simp [zeroState]
  constructor
  · intro t
    simp [zeroState]
  · intro t
    simp [zeroState]

end NSProducerFirst.P1Concrete
