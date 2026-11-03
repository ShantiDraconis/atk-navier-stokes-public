import open_math.ActualNSToSignedGainCore.P1_RieszH1ToL3
import open_math.ActualNSToSignedGainCore.P1_DivCurlIdentity

/-!
NS-FORCING-001 / global integrability gate.

SmoothNSState supplies smoothness and the PDE, but not global L2/H1 finiteness
on R3.  The material chain must therefore carry these hypotheses explicitly;
otherwise the raw integrals used by enstrophy/palinstrophy do not by themselves
certify MemLp.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

structure VorticityH1Gate
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f) where
  omegaL2 :
    ∀ t : ℝ,
      MemLp (vorticity s.velocity t) 2
        (volume : Measure Space)
  gradOmegaL2 :
    ∀ t : ℝ,
      MemLp
        (fderiv ℝ (fun x : Space => vorticity s.velocity t x))
        2
        (volume : Measure Space)
  omegaSmooth :
    ∀ t : ℝ,
      ContDiff ℝ 1 (vorticity s.velocity t)

def VORTICITY_H1_OPEN_MATH
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f) : Prop :=
  Nonempty (VorticityH1Gate s)

/-- The H1 gate gives the exact L3 vorticity input used by Holder. -/
theorem vorticity_memLp_three_of_H1_gate
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    {s : SmoothNSState times ν f}
    (H : VORTICITY_H1_OPEN_MATH s)
    (t : ℝ) :
    MemLp (vorticity s.velocity t) 3
      (volume : Measure Space) := by
  rcases H with ⟨P⟩
  exact (h1_to_l3_compression
    (P.omegaSmooth t)
    (P.omegaL2 t)
    (P.gradOmegaL2 t)).1

/-- Exact integral identities behind the concrete observables. -/
theorem enstrophy_eq_integral_norm_sq
    (u : VelocityField) (t : ℝ) :
    enstrophy u t =
      ∫ x : Space, ‖vorticity u t x‖ ^ 2 := by
  rfl

theorem palinstrophy_eq_integral_norm_sq
    (u : VelocityField) (t : ℝ) :
    palinstrophy u t =
      ∫ x : Space,
        ‖fderiv ℝ (fun y : Space => vorticity u t y) x‖ ^ 2 := by
  rfl

end NSProducerFirst.P1Concrete
