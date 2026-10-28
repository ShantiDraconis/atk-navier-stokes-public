import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-- Positive and negative parts are kept separate so cancellation is not destroyed
    before it has been tested. -/
def positivePart (x : ℝ) : ℝ := max x 0

def negativePart (x : ℝ) : ℝ := max (-x) 0

theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := by
  simp [positivePart]

theorem negativePart_nonneg (x : ℝ) : 0 ≤ negativePart x := by
  simp [negativePart]

theorem signed_part_decomposition (x : ℝ) :
    x = positivePart x - negativePart x := by
  rcases le_total 0 x with hx | hx
  · simp [positivePart, negativePart, hx, neg_nonpos.mpr hx]
  · have hnx : 0 ≤ -x := neg_nonneg.mpr hx
    simp [positivePart, negativePart, hx, hnx]

/-- Pointwise aligned stretching density `|ω|² (ξᵀ S ξ)`, represented by
    a nonnegative weight `omegaSq` and the signed aligned strain scalar. -/
def signedDensity (omegaSq aligned : ℝ) : ℝ := omegaSq * aligned

def positiveDensity (omegaSq aligned : ℝ) : ℝ :=
  omegaSq * positivePart aligned

def negativeDensity (omegaSq aligned : ℝ) : ℝ :=
  omegaSq * negativePart aligned

theorem density_decomposition (omegaSq aligned : ℝ) :
    signedDensity omegaSq aligned =
      positiveDensity omegaSq aligned - negativeDensity omegaSq aligned := by
  unfold signedDensity positiveDensity negativeDensity
  calc
    omegaSq * aligned =
        omegaSq * (positivePart aligned - negativePart aligned) :=
      congrArg (fun x : ℝ => omegaSq * x) (signed_part_decomposition aligned)
    _ = omegaSq * positivePart aligned - omegaSq * negativePart aligned := by ring

theorem positiveDensity_nonneg
    {omegaSq aligned : ℝ} (hω : 0 ≤ omegaSq) :
    0 ≤ positiveDensity omegaSq aligned := by
  exact mul_nonneg hω (positivePart_nonneg aligned)

theorem negativeDensity_nonneg
    {omegaSq aligned : ℝ} (hω : 0 ≤ omegaSq) :
    0 ≤ negativeDensity omegaSq aligned := by
  exact mul_nonneg hω (negativePart_nonneg aligned)

/-- Signed stretching is bounded above by the positive aligned contribution,
    without replacing the signed quantity by its absolute value. -/
theorem signedDensity_le_positiveDensity
    {omegaSq aligned : ℝ} (hω : 0 ≤ omegaSq) :
    signedDensity omegaSq aligned ≤ positiveDensity omegaSq aligned := by
  rw [density_decomposition]
  have hn := negativeDensity_nonneg (omegaSq := omegaSq) (aligned := aligned) hω
  linarith

/-- Absolute value loses the signed cancellation and is controlled only by the sum. -/
theorem abs_signedDensity_le_sum
    {omegaSq aligned : ℝ} (hω : 0 ≤ omegaSq) :
    |signedDensity omegaSq aligned| ≤
      positiveDensity omegaSq aligned + negativeDensity omegaSq aligned := by
  rw [density_decomposition]
  have hp := positiveDensity_nonneg (omegaSq := omegaSq) (aligned := aligned) hω
  have hn := negativeDensity_nonneg (omegaSq := omegaSq) (aligned := aligned) hω
  rw [abs_sub_comm]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end MPrivate.NS.ThirdCoefficient
