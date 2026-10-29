import Mathlib

/-!
NS-FORCING-001 / concrete PDE observables.

This file introduces no closure hypothesis and no certificate interface.
It defines the actual three-dimensional velocity/vorticity observables that
feed the already-frozen `NSProducerFirst.EnstrophyData`.

It is intended to be compiled after the frozen ProducerFirst definitions.
-/


noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NSProducerFirst.P1Concrete

/-- Physical Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Time-dependent velocity field on R^3. -/
abbrev VelocityField := ℝ × Space → Space

/-- Standard coordinate vector. -/
def coordinateVector (i : Fin 3) : Space :=
  EuclideanSpace.single i 1

/-- Spatial Frechet derivative at fixed physical time. -/
def spatialDerivative
    (u : VelocityField) (t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  fderiv ℝ (fun y : Space => u (t, y)) x

/-- One matrix entry of a spatial derivative. -/
def derivativeEntry (i j : Fin 3) :
    (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp
    (ContinuousLinearMap.apply ℝ Space (coordinateVector i))

/-- Antisymmetric Jacobian identified with the physical curl vector. -/
def curlLinear : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (derivativeEntry 1 2 - derivativeEntry 2 1).smulRight (coordinateVector 0) +
  (derivativeEntry 2 0 - derivativeEntry 0 2).smulRight (coordinateVector 1) +
  (derivativeEntry 0 1 - derivativeEntry 1 0).smulRight (coordinateVector 2)

/-- Physical vorticity omega = curl u. -/
def vorticity (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  curlLinear (spatialDerivative u t x)

/-- Enstrophy density |omega|^2. -/
def enstrophyDensity (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  ‖vorticity u t x‖ ^ 2

/-- Palinstrophy density |grad omega|^2, using the operator norm of the
spatial Frechet derivative of vorticity. -/
def palinstrophyDensity (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  ‖fderiv ℝ (fun y : Space => vorticity u t y) x‖ ^ 2

/-- Signed vortex-stretching density omega · ((grad u) omega).

For a smooth velocity field the skew part of grad u contributes zero to this
quadratic form, so this is the standard signed strain/vorticity production
integrand without discarding cancellation by an absolute value.
-/
def stretchingDensity (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  @inner ℝ Space _ (vorticity u t x)
    (spatialDerivative u t x (vorticity u t x))

/-- Concrete enstrophy. -/
def enstrophy (u : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, enstrophyDensity u t x

/-- Concrete palinstrophy. -/
def palinstrophy (u : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, palinstrophyDensity u t x

/-- Concrete signed vortex-stretching production. -/
def stretching (u : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, stretchingDensity u t x

theorem enstrophy_nonneg (u : VelocityField) (t : ℝ) :
    0 ≤ enstrophy u t := by
  unfold enstrophy enstrophyDensity
  exact integral_nonneg fun _ => sq_nonneg _

theorem palinstrophy_nonneg (u : VelocityField) (t : ℝ) :
    0 ≤ palinstrophy u t := by
  unfold palinstrophy palinstrophyDensity
  exact integral_nonneg fun _ => sq_nonneg _

end NSProducerFirst.P1Concrete
