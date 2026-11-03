import open_math.ActualNSToSignedGainCore.P1_DivCurlIdentity

/-!
NS-FORCING-001 / coordinate mincut for the local div-curl identity.

This file does not assume the vector identity.  It exposes equality in R3 as
three scalar coordinate equalities, so the remaining proof can be attacked
componentwise without reopening harmonic analysis.
-/

noncomputable section

namespace NSProducerFirst.P1Concrete

/-- Equality of two physical R3 vectors is equivalent to equality of the three
coordinates. -/
theorem space_ext_three
    {a b : Space}
    (h0 : a 0 = b 0)
    (h1 : a 1 = b 1)
    (h2 : a 2 = b 2) :
    a = b := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Componentwise form of the local div-curl target. -/
def DivCurlCoordinateTarget
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    (t : ℝ)
    (x : Space) : Prop :=
  (spatialLaplacian s.velocity t x) 0 =
      (- curlVorticity s.velocity t x) 0 ∧
  (spatialLaplacian s.velocity t x) 1 =
      (- curlVorticity s.velocity t x) 1 ∧
  (spatialLaplacian s.velocity t x) 2 =
      (- curlVorticity s.velocity t x) 2

/-- Three scalar coordinate identities are sufficient for the vector identity. -/
theorem divCurl_of_coordinate_target
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (x : Space)
    (h : DivCurlCoordinateTarget s t x) :
    spatialLaplacian s.velocity t x =
      - curlVorticity s.velocity t x := by
  rcases h with ⟨h0, h1, h2⟩
  exact space_ext_three h0 h1 h2

/-- Conversely, the vector identity gives exactly the three scalar targets. -/
theorem coordinate_target_of_divCurl
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (x : Space)
    (h :
      spatialLaplacian s.velocity t x =
        - curlVorticity s.velocity t x) :
    DivCurlCoordinateTarget s t x := by
  constructor
  · exact congrArg (fun v : Space => v 0) h
  constructor
  · exact congrArg (fun v : Space => v 1) h
  · exact congrArg (fun v : Space => v 2) h

theorem divCurl_iff_coordinate_target
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (x : Space) :
    spatialLaplacian s.velocity t x =
        - curlVorticity s.velocity t x ↔
      DivCurlCoordinateTarget s t x := by
  constructor
  · exact coordinate_target_of_divCurl s x
  · exact divCurl_of_coordinate_target s x

end NSProducerFirst.P1Concrete
