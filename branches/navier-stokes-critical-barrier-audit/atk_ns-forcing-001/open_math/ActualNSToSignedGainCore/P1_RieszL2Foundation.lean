import open_math.ActualNSToSignedGainCore.P1_ConcreteObservables

/-!
NS-FORCING-001 / L2 Riesz backend frontier.

The pinned Mathlib v4.19.0 does not expose the later
`Mathlib.Analysis.Fourier.LpSpace` API used by the previous implementation.
Rather than manufacturing a Fourier operator, this module records the exact
operator-level data needed downstream.  An inhabitant is a material/formal
backend obligation.
-/

noncomputable section

open MeasureTheory

namespace NSProducerFirst.P1Concrete

structure P1RieszL2Backend where
  doubleRiesz :
    Fin 3 → Fin 3 →
      Lp ℂ 2 (volume : Measure Space) →
      Lp ℂ 2 (volume : Measure Space)
  contraction :
    ∀ i j f, ‖doubleRiesz i j f‖ ≤ ‖f‖

def P1_RIESZ_L2_BACKEND_OPEN_MATH : Prop :=
  Nonempty P1RieszL2Backend

theorem p1RieszL2Backend_contraction
    (B : P1RieszL2Backend)
    (i j : Fin 3)
    (f : Lp ℂ 2 (volume : Measure Space)) :
    ‖B.doubleRiesz i j f‖ ≤ ‖f‖ :=
  B.contraction i j f

#print axioms NSProducerFirst.P1Concrete.p1RieszL2Backend_contraction

end NSProducerFirst.P1Concrete
