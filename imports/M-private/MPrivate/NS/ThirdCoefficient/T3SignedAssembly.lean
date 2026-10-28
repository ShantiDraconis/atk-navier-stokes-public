import Mathlib
import MPrivate.NS.ThirdCoefficient.AlignmentDepletionInequality

namespace MPrivate.NS.ThirdCoefficient

/-!
# T3SignedAssembly

Pure assembly logic for the G1-flex / ThirdCoefficient T3 target.

This file does not prove any Navier--Stokes estimate. It identifies sufficient
subgates whose proofs would assemble into the one-sided signed estimate

  V ≤ theta * nu * Z + C * a3 * Y.

No `sorry`, no `axiom`, and no existential claim for a ThirdCoefficient.
-/

/-- Four-way decomposition used by the first signed attack. -/
def SignedT3Decomposition
    (V Vgood Vlow Vcross Valign : ℝ) : Prop :=
  V = Vgood + Vlow + Vcross + Valign

/-- The dissipative/signed part is genuinely absorbed. -/
def GoodPartBound
    (Vgood theta nu Z : ℝ) : Prop :=
  Vgood ≤ theta * nu * Z

/-- Low-frequency residue has already factored through `Y`. -/
def LowPartBound
    (Vlow C aLow Y : ℝ) : Prop :=
  Vlow ≤ C * aLow * Y

/-- Cross-frequency residue has already factored through `Y`. -/
def CrossPartBound
    (Vcross C aCross Y : ℝ) : Prop :=
  Vcross ≤ C * aCross * Y

/-- Alignment-sensitive residue has already factored through `Y`. -/
def AlignPartBound
    (Valign C aAlign Y : ℝ) : Prop :=
  Valign ≤ C * aAlign * Y

/-- Algebraic assembly of the signed T3 estimate.

The analytic content is entirely in the four hypotheses. In particular this
lemma must not be cited as proving any one of them for actual NSE solutions. -/
theorem assemble_signed_T3
    (V Vgood Vlow Vcross Valign theta nu Z C aLow aCross aAlign Y : ℝ)
    (hdec : SignedT3Decomposition V Vgood Vlow Vcross Valign)
    (hgood : GoodPartBound Vgood theta nu Z)
    (hlow : LowPartBound Vlow C aLow Y)
    (hcross : CrossPartBound Vcross C aCross Y)
    (halign : AlignPartBound Valign C aAlign Y) :
    V ≤ theta * nu * Z + C * (aLow + aCross + aAlign) * Y := by
  unfold SignedT3Decomposition at hdec
  unfold GoodPartBound at hgood
  unfold LowPartBound at hlow
  unfold CrossPartBound at hcross
  unfold AlignPartBound at halign
  rw [hdec]
  nlinarith

/-- G1-flex still requires a strict surviving dissipative margin. -/
def StrictDissipativeMargin (theta : ℝ) : Prop :=
  0 ≤ theta ∧ theta < 1

/-- Every component is pointwise no better than the same rejected barrier. -/
def AllComponentsDominate
    (aLow aCross aAlign oldBarrier : ℝ → ℝ) : Prop :=
  DominatesKnownBarrier aLow oldBarrier ∧
  DominatesKnownBarrier aCross oldBarrier ∧
  DominatesKnownBarrier aAlign oldBarrier

/-- If every component dominates the same rejected barrier, then their sum also
    dominates it.  This is a sound reason to reject the decomposed coefficient
    on pointwise-size grounds. -/
theorem decomposed_dominates_oldBarrier
    (aLow aCross aAlign oldBarrier : ℝ → ℝ)
    (h : AllComponentsDominate aLow aCross aAlign oldBarrier) :
    DominatesKnownBarrier
      (decomposedA3 aLow aCross aAlign) oldBarrier := by
  rcases h.1 with ⟨cL, hcL, hL⟩
  rcases h.2.1 with ⟨cC, hcC, hC⟩
  rcases h.2.2 with ⟨cA, hcA, hA⟩
  refine ⟨cL + cC + cA, by linarith, ?_⟩
  intro t
  unfold decomposedA3
  have h1 := hL t
  have h2 := hC t
  have h3 := hA t
  nlinarith

/-- Exact frontier after the assembly logic: these four propositions are the
first analytic obligations. -/
structure T3AnalyticFrontier where
  good_absorption : Prop
  low_frequency_factorization : Prop
  cross_frequency_factorization : Prop
  alignment_factorization : Prop

end MPrivate.NS.ThirdCoefficient
