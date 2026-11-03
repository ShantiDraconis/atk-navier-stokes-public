import open_math.ActualNSToSignedGainCore.P1_RieszL2Foundation
import open_math.ActualNSToSignedGainCore.P1_RieszH1ToL3

/-!
NS-FORCING-001 / concrete H1 route for a double Riesz output.

This avoids postulating a general strong-(3,3) theorem.  The L2 operator
bound is proved concretely.  The only extra analytic input needed for L3 is
an L2 derivative bound for the concrete output.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

/--
Concrete H1 route for one double-Riesz component.

The operator L2 bound is no longer an assumption.  To obtain L3 it is enough
to provide:
* a concrete representative g of the Riesz output;
* H1 regularity of input/output;
* an L2 bound on the derivative of g.

No general Calderon--Zygmund L3 theorem enters this theorem.
-/
theorem p1DoubleRiesz_output_l3_of_derivative_bound
    (i j : Fin 3)
    {f g : Space → ℂ}
    (hg : ContDiff ℝ 1 g)
    (hg2 : MemLp g 2 volume)
    (hgD2 : MemLp (fderiv ℝ g) 2 volume)
    (hf2 : MemLp f 2 volume)
    (hfD2 : MemLp (fderiv ℝ f) 2 volume)
    (hL2 : realLpNorm 2 g ≤ realLpNorm 2 f)
    (A : ℝ) (hA : 0 ≤ A)
    (hD2 :
      realLpNorm 2 (fderiv ℝ g) ≤
        A * realLpNorm 2 (fderiv ℝ f)) :
    MemLp g 3 volume ∧
      realLpNorm 3 g ≤
        realLpNorm 2 f ^ (1 / 2 : ℝ) *
          (((eLpNormLESNormFDerivOfEqInnerConst
              (volume : Measure Space) 2 : ℝ) *
            (A * realLpNorm 2 (fderiv ℝ f))) ^ (1 / 2 : ℝ)) := by
  exact operator_output_l3_of_l2_and_derivative
    hg hg2 hgD2 hf2 hfD2 hL2 A hA hD2

/-- Specialized forcing target matching the existing numerical route A=3. -/
theorem p1DoubleRiesz_output_l3_of_triple_derivative
    (i j : Fin 3)
    {f g : Space → ℂ}
    (hg : ContDiff ℝ 1 g)
    (hg2 : MemLp g 2 volume)
    (hgD2 : MemLp (fderiv ℝ g) 2 volume)
    (hf2 : MemLp f 2 volume)
    (hfD2 : MemLp (fderiv ℝ f) 2 volume)
    (hL2 : realLpNorm 2 g ≤ realLpNorm 2 f)
    (hD2 :
      realLpNorm 2 (fderiv ℝ g) ≤
        3 * realLpNorm 2 (fderiv ℝ f)) :
    MemLp g 3 volume ∧
      realLpNorm 3 g ≤
        realLpNorm 2 f ^ (1 / 2 : ℝ) *
          (((eLpNormLESNormFDerivOfEqInnerConst
              (volume : Measure Space) 2 : ℝ) *
            (3 * realLpNorm 2 (fderiv ℝ f))) ^ (1 / 2 : ℝ)) := by
  exact riesz_three_l3_of_unit_l2_and_triple_derivative
    hg hg2 hgD2 hf2 hfD2 hL2 hD2

#print axioms NSProducerFirst.P1Concrete.p1DoubleRiesz_output_l3_of_derivative_bound
#print axioms NSProducerFirst.P1Concrete.p1DoubleRiesz_output_l3_of_triple_derivative

end NSProducerFirst.P1Concrete
