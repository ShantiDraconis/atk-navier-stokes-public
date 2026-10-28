import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# DirectionalCoherenceNoGo

Directional coherence alone does not control the sign of vortex stretching.
A direction may be perfectly coherent while aligned with the most expansive
strain eigendirection.

We encode the diagonal example

  S = diag(2,-1,-1),  xi = e1,

for which an angular defect relative to e1 vanishes but
`xi^T S xi = 2 > 0`.
-/

/-- Quadratic form for a diagonal strain tensor. -/
def diagonalAlignedStrain
    (l1 l2 l3 x1 x2 x3 : ℝ) : ℝ :=
  l1 * x1^2 + l2 * x2^2 + l3 * x3^2

/-- Simple direction-only defect from the first axis. -/
def e1DirectionDefect (x2 x3 : ℝ) : ℝ :=
  x2^2 + x3^2

/-- Perfect directional coherence with e1. -/
theorem e1_has_zero_direction_defect :
    e1DirectionDefect 0 0 = 0 := by
  norm_num [e1DirectionDefect]

/-- The same direction is maximally expansive for diag(2,-1,-1). -/
theorem e1_has_positive_aligned_strain :
    diagonalAlignedStrain 2 (-1) (-1) 1 0 0 = 2 := by
  norm_num [diagonalAlignedStrain]

/-- Combined countercertificate: zero directional defect coexists with strictly
positive aligned stretching. -/
theorem direction_only_coherence_not_signed_depletion :
    e1DirectionDefect 0 0 = 0 ∧
    0 < diagonalAlignedStrain 2 (-1) (-1) 1 0 0 := by
  constructor
  · exact e1_has_zero_direction_defect
  · norm_num [diagonalAlignedStrain]

/-- Any viable alignment certificate must include signed strain coupling, not
only direction-direction coherence. -/
structure JointAlignmentRequirement where
  directionalDefect : Prop
  positiveStrainCoupling : Prop
  jointSignedEstimate : Prop
  derivedFromActualNS : Prop

inductive DirectionOnlyStatus where
  | formalRefutedAsSufficient
  | mayRemainAuxiliary
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
