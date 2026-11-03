import open_math.ActualNSToSignedGainCore.P1_StretchingHolder
import open_math.ActualNSToSignedGainCore.P1_WholeSpaceSobolev
import open_math.ActualNSToSignedGainCore.P1_LpInterpolation
import open_math.ActualNSToSignedGainCore.P1_ConcretePDE

/-!
NS-FORCING-001 / unique remaining harmonic-analysis producer.

All pointwise, Holder, interpolation, whole-space Sobolev and Young algebra
has already been isolated upstream.  This file states the exact concrete
div-curl / Calderon-Zygmund theorem needed to close the L3 stretching chain.

There is exactly one open proof below; targeted compilation reaches this file.  It is not an interface wrapper: its
conclusion is the concrete L3 bound on the already-defined spatial derivative
and vorticity.
-/


noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

/--
Concrete R3 div-curl / Calderon-Zygmund producer.

The L2 velocity premise fixes the zero-frequency/harmonic ambiguity on R3.
The divergence-free identity and vorticity are the actual concrete operators
defined in P1_ConcretePDE / P1_ConcreteObservables.

The constant is universal for the fixed physical dimension.
-/
theorem p1_rieszCZ_L3
    (u : VelocityField)
    (t : ℝ)
    (hu2 : MemLp (fun x => u (t, x)) 2 (volume : Measure Space))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hω3 : MemLp (vorticity u t) 3 (volume : Measure Space)) :
    ∃ C_CZ : ℝ,
      0 ≤ C_CZ ∧
      MemLp (fun x => spatialDerivative u t x) 3 (volume : Measure Space) ∧
      (eLpNorm (fun x => spatialDerivative u t x) 3
          (volume : Measure Space)).toReal ≤
        C_CZ *
          (eLpNorm (vorticity u t) 3
            (volume : Measure Space)).toReal := by
  /-
  OPEN_MATH / HARMONIC ANALYSIS ONLY.

  Required proof:
    1. Fourier/div-curl identity for divergence-free u:
         ∂_j u_i = finite linear combination of R_j R_k omega_l.
    2. Define the Riesz multipliers on the concrete R3 Fourier side.
    3. Prove strong (3,3) boundedness for those multipliers.
    4. Sum the finitely many coordinate components and convert to the
       operator norm of spatialDerivative.

  The L2 premise removes the harmonic/zero-frequency ambiguity.
  No Navier-Stokes continuation criterion or signed-gain estimate may enter.
  -/
  sorry

/--
For an actual concrete NSE state, the divergence-free premise required by
p1_rieszCZ_L3 is already supplied by the PDE carrier at every t in times.
-/
theorem smoothNSState_divergence_free
    {times : Set ℝ}
    {ν : ℝ}
    {f : VelocityField}
    (s : SmoothNSState times ν f)
    {t : ℝ}
    (ht : t ∈ times) :
    ∀ x, spatialDivergence s.velocity t x = 0 := by
  exact s.satisfies_nse.1 t ht

#print axioms NSProducerFirst.P1Concrete.smoothNSState_divergence_free

end NSProducerFirst.P1Concrete
