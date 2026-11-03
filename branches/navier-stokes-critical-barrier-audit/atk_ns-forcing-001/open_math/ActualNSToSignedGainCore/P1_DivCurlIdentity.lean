import open_math.ActualNSToSignedGainCore.P1_ConcretePDE

/-!
NS-FORCING-001 / first exact Riesz-CZ subquestion.

This isolates the purely local vector-calculus identity before any Fourier or
Lp boundedness argument.
-/

noncomputable section

open scoped ContDiff

namespace NSProducerFirst.P1Concrete

/-- A fixed-time spatial slice inherits smoothness from the concrete spacetime field. -/
theorem spatialSlice_contDiff
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (ht : t ∈ times) :
    ContDiff ℝ ∞ (fun x : Space => s.velocity (t, x)) := by
  exact s.velocity_smooth.comp_contDiff
    (contDiff_prodMk_right t)
    (fun x => ⟨ht, Set.mem_univ x⟩)

/-- Mixed spatial second derivatives commute for every concrete smooth NSE slice. -/
theorem spatialSlice_second_derivative_symmetric
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (ht : t ∈ times)
    (x : Space) :
    IsSymmSndFDerivAt ℝ (fun y : Space => s.velocity (t, y)) x := by
  exact (spatialSlice_contDiff s ht).contDiffAt.isSymmSndFDerivAt (by simp)

/-- Curl of the concrete vorticity slice. -/
def curlVorticity
    (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  curlLinear (fderiv ℝ (fun y : Space => vorticity u t y) x)

/--
Exact local div-curl identity for the concrete operators:
for a smooth divergence-free slice,
  Δu = - curl(curl u).
-/
theorem spatialLaplacian_eq_neg_curlVorticity
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (ht : t ∈ times) :
    ∀ x,
      spatialLaplacian s.velocity t x =
        - curlVorticity s.velocity t x := by
  sorry

end NSProducerFirst.P1Concrete
