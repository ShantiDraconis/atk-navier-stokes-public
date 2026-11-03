import open_math.ActualNSToSignedGainCore.P1_DivCurlIdentity

/-!
NS-FORCING-001 / mixed-partial commutation on the concrete R3 basis.

This is the exact local calculus input for the div-curl identity.  It is
derived directly from the smooth NSE slice and Mathlib's
IsSymmSndFDerivAt.eq, with no harmonic-analysis assumption.
-/

noncomputable section

namespace NSProducerFirst.P1Concrete

/-- All coordinate mixed second derivatives of a concrete smooth NSE slice
commute. -/
theorem coordinate_mixed_second_derivative_commutes
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (ht : t ∈ times)
    (x : Space)
    (i j : Fin 3) :
    fderiv ℝ
        (fderiv ℝ (fun y : Space => s.velocity (t, y)))
        x (coordinateVector i) (coordinateVector j)
      =
    fderiv ℝ
        (fderiv ℝ (fun y : Space => s.velocity (t, y)))
        x (coordinateVector j) (coordinateVector i) := by
  exact
    (spatialSlice_second_derivative_symmetric s ht x).eq
      (coordinateVector i) (coordinateVector j)

/-- Scalar component form, ready for the three explicit curl-curl
coordinates. -/
theorem coordinate_mixed_second_derivative_component_commutes
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (ht : t ∈ times)
    (x : Space)
    (i j k : Fin 3) :
    (fderiv ℝ
        (fderiv ℝ (fun y : Space => s.velocity (t, y)))
        x (coordinateVector i) (coordinateVector j)) k
      =
    (fderiv ℝ
        (fderiv ℝ (fun y : Space => s.velocity (t, y)))
        x (coordinateVector j) (coordinateVector i)) k := by
  exact congrArg
    (fun v : Space => v k)
    (coordinate_mixed_second_derivative_commutes s ht x i j)

#print axioms NSProducerFirst.P1Concrete.coordinate_mixed_second_derivative_commutes
#print axioms NSProducerFirst.P1Concrete.coordinate_mixed_second_derivative_component_commutes

end NSProducerFirst.P1Concrete
