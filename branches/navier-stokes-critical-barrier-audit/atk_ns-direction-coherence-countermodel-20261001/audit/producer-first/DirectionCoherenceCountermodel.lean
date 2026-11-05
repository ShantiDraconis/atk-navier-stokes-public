import Mathlib
import formal.g1.lean.G1Depletion

namespace G1.DirectionCoherenceCountermodel

/--
A one-point, one-time model in which the high-vorticity antecedent of
BetaHalfCoherence is false, so directional coherence holds vacuously, while
stretching strictly exceeds palinstrophy.
-/
def counterData : G1.Data where
  Time := Unit
  Point := Unit
  omegaNorm := fun _ _ => 0
  distance := fun _ _ => 0
  sinAngle := fun _ _ _ => 0
  stretching := fun _ => 2
  palinstrophy := fun _ => 1
  enstrophyDerivative := fun _ => 0

theorem betaHalfCoherence_holds
    (M c C : ℝ)
    (hM : 0 < M)
    (hc : 0 < c) :
    G1.BetaHalfCoherence counterData M c C := by
  intro t x y hx hy hdist
  change 0 ≤ C * Real.sqrt 0
  simp

theorem closedDepletion_fails
    (δ : ℝ)
    (hδ : 0 < δ) :
    ¬ G1.ClosedDepletion counterData δ := by
  intro h
  rcases h with ⟨_, hstretch⟩
  have hs := hstretch ()
  change (2 : ℝ) ≤ (1 - δ) * 1 at hs
  linarith

/--
Directional beta=1/2 coherence, even with positive parameter choices, does
not imply ClosedDepletion for arbitrary G1.Data.
Hence a genuine bridge must use additional flow-coupled hypotheses
(strain/joint information, weighted-tail control, or equivalent structure).
-/
theorem no_universal_direction_only_bridge :
    ¬ (∀ (D : G1.Data) (M c C δ : ℝ),
        0 < M →
        0 < c →
        0 < δ →
        G1.BetaHalfCoherence D M c C →
        G1.ClosedDepletion D δ) := by
  intro H
  have hcoh : G1.BetaHalfCoherence counterData 1 1 1 :=
    betaHalfCoherence_holds 1 1 1 (by norm_num) (by norm_num)
  have hclosed : G1.ClosedDepletion counterData 1 :=
    H counterData 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) hcoh
  exact closedDepletion_fails 1 (by norm_num) hclosed

#print axioms G1.DirectionCoherenceCountermodel.betaHalfCoherence_holds
#print axioms G1.DirectionCoherenceCountermodel.closedDepletion_fails
#print axioms G1.DirectionCoherenceCountermodel.no_universal_direction_only_bridge

end G1.DirectionCoherenceCountermodel
