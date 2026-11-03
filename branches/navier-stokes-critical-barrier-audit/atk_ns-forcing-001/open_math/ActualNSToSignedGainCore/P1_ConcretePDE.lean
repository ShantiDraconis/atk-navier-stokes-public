import open_math.ActualNSToSignedGainCore.P1_ConcreteObservables

/-!
NS-FORCING-001 / concrete Navier--Stokes carrier.

No closure estimate is postulated here.  This file records the literal
three-dimensional incompressible Navier--Stokes differential operators on the
same concrete velocity fields used by P1_ConcreteObservables.
-/


noncomputable section

open Set
open scoped BigOperators ContDiff

namespace NSProducerFirst.P1Concrete

abbrev SpaceTime := ℝ × Space
abbrev PressureField := SpaceTime → ℝ

def temporalDerivative
    (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun s : ℝ => u (s, x)) t 1

def advection
    (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative u t x (u (t, x))

def spatialDivergence
    (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3,
    (spatialDerivative u t x (coordinateVector i)) i

def pressureGradient
    (p : PressureField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    (fderiv ℝ (fun y : Space => p (t, y)) x (coordinateVector i)) •
      coordinateVector i

def spatialLaplacian
    (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    fderiv ℝ
      (fun y : Space =>
        spatialDerivative u t y (coordinateVector i))
      x (coordinateVector i)

/-- Exact incompressible NSE residual with viscosity nu and forcing f:
    u_t + (u dot grad)u - nu Delta u + grad p - f. -/
def navierStokesResidual
    (ν : ℝ)
    (u : VelocityField)
    (p : PressureField)
    (f : VelocityField)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative u t x +
    advection u t x -
    ν • spatialLaplacian u t x +
    pressureGradient p t x -
    f (t, x)

/-- Literal PDE predicate on a time set.  This is a definition, not an
assumption that any field satisfies it. -/
def SatisfiesNSEOn
    (times : Set ℝ)
    (ν : ℝ)
    (u : VelocityField)
    (p : PressureField)
    (f : VelocityField) : Prop :=
  (∀ t ∈ times, ∀ x : Space, spatialDivergence u t x = 0) ∧
  (∀ t ∈ times, ∀ x : Space,
    navierStokesResidual ν u p f t x = 0)

/-- A concrete smooth NSE state.  The fields themselves are the state;
the proof fields certify only literal PDE and smoothness.  No signed-depletion
estimate, bulk/tail estimate, or continuation criterion is included. -/
structure SmoothNSState
    (times : Set ℝ)
    (ν : ℝ)
    (f : VelocityField) where
  velocity : VelocityField
  pressure : PressureField
  velocity_smooth :
    ContDiffOn ℝ ∞ velocity (times ×ˢ (Set.univ : Set Space))
  pressure_smooth :
    ContDiffOn ℝ ∞ pressure (times ×ˢ (Set.univ : Set Space))
  satisfies_nse :
    SatisfiesNSEOn times ν velocity pressure f

end NSProducerFirst.P1Concrete
