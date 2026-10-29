import Mathlib
import CriticalBarrier.K1aPDELift

namespace CriticalBarrier.KernelPromotedG1Assembly

/-!
Kernel-promoted reuse of the algebraic NS assembly previously verified in
ShantiDraconis/M-private:
- G1FlexFromThirdCoefficient
- ThreeGateToG1Flex

This file deliberately does NOT construct the open analytic bridge from an
actual Navier-Stokes solution to the block estimates. It removes only the
already-solved downstream assembly.
-/

def EnstrophyBalance (yPrime nu Z V : ℝ) : Prop :=
  (1 / 2 : ℝ) * yPrime + nu * Z = V

def G1FlexEstimate (V theta nu Z a Y : ℝ) : Prop :=
  V ≤ theta * nu * Z + a * Y

theorem balance_and_G1flex_give_differential_inequality
    (yPrime nu Z V theta a Y : ℝ)
    (hbal : EnstrophyBalance yPrime nu Z V)
    (hg1 : G1FlexEstimate V theta nu Z a Y) :
    (1 / 2 : ℝ) * yPrime + (1 - theta) * nu * Z ≤ a * Y := by
  unfold EnstrophyBalance at hbal
  unfold G1FlexEstimate at hg1
  linarith

structure ThreeGatePointwiseData where
  V : ℝ
  Vgood : ℝ
  Vlow : ℝ
  Vcross : ℝ
  Valign : ℝ
  Z : ℝ
  Y : ℝ
  epsGood : ℝ
  epsLow : ℝ
  epsCross : ℝ
  epsAlign : ℝ
  C : ℝ
  aLow : ℝ
  aCross : ℝ
  aAlign : ℝ

def totalEpsilon (d : ThreeGatePointwiseData) : ℝ :=
  d.epsGood + d.epsLow + d.epsCross + d.epsAlign

def pointwiseA3 (d : ThreeGatePointwiseData) : ℝ :=
  d.aLow + d.aCross + d.aAlign

def ThreeGatePointwiseCertified (d : ThreeGatePointwiseData) : Prop :=
  d.V = d.Vgood + d.Vlow + d.Vcross + d.Valign ∧
  d.Vgood ≤ d.epsGood * d.Z ∧
  d.Vlow ≤ d.epsLow * d.Z + d.C * d.aLow * d.Y ∧
  d.Vcross ≤ d.epsCross * d.Z + d.C * d.aCross * d.Y ∧
  d.Valign ≤ d.epsAlign * d.Z + d.C * d.aAlign * d.Y

theorem three_gate_pointwise_assembles
    (d : ThreeGatePointwiseData)
    (h : ThreeGatePointwiseCertified d) :
    d.V ≤ totalEpsilon d * d.Z + d.C * pointwiseA3 d * d.Y := by
  rcases h with ⟨hdec, hgood, hlow, hcross, halign⟩
  unfold totalEpsilon pointwiseA3
  rw [hdec]
  linarith

noncomputable def pointwiseTheta (d : ThreeGatePointwiseData) (nu : ℝ) : ℝ :=
  totalEpsilon d / nu

theorem pointwiseTheta_nonnegative
    (d : ThreeGatePointwiseData)
    (nu : ℝ)
    (hnu : 0 < nu)
    (heps : 0 ≤ totalEpsilon d) :
    0 ≤ pointwiseTheta d nu := by
  unfold pointwiseTheta
  exact div_nonneg heps (le_of_lt hnu)

theorem pointwiseTheta_strictly_less_than_one
    (d : ThreeGatePointwiseData)
    (nu : ℝ)
    (hnu : 0 < nu)
    (heps : totalEpsilon d < nu) :
    pointwiseTheta d nu < 1 := by
  unfold pointwiseTheta
  exact (div_lt_one hnu).2 heps

theorem three_gate_gives_G1flex
    (d : ThreeGatePointwiseData)
    (nu : ℝ)
    (hnu : 0 < nu)
    (h : ThreeGatePointwiseCertified d) :
    G1FlexEstimate d.V (pointwiseTheta d nu) nu d.Z
      (d.C * pointwiseA3 d) d.Y := by
  unfold G1FlexEstimate pointwiseTheta
  have hT3 := three_gate_pointwise_assembles d h
  have hnune : nu ≠ 0 := ne_of_gt hnu
  field_simp [hnune]
  nlinarith

theorem three_gate_plus_balance_gives_differential
    (d : ThreeGatePointwiseData)
    (nu yPrime : ℝ)
    (hnu : 0 < nu)
    (hT3 : ThreeGatePointwiseCertified d)
    (hbal : EnstrophyBalance yPrime nu d.Z d.V) :
    (1 / 2 : ℝ) * yPrime +
      (1 - pointwiseTheta d nu) * nu * d.Z ≤
      (d.C * pointwiseA3 d) * d.Y := by
  exact balance_and_G1flex_give_differential_inequality
    yPrime nu d.Z d.V (pointwiseTheta d nu)
    (d.C * pointwiseA3 d) d.Y hbal
    (three_gate_gives_G1flex d nu hnu hT3)

#print axioms CriticalBarrier.KernelPromotedG1Assembly.balance_and_G1flex_give_differential_inequality
#print axioms CriticalBarrier.KernelPromotedG1Assembly.three_gate_pointwise_assembles
#print axioms CriticalBarrier.KernelPromotedG1Assembly.pointwiseTheta_nonnegative
#print axioms CriticalBarrier.KernelPromotedG1Assembly.pointwiseTheta_strictly_less_than_one
#print axioms CriticalBarrier.KernelPromotedG1Assembly.three_gate_gives_G1flex
#print axioms CriticalBarrier.KernelPromotedG1Assembly.three_gate_plus_balance_gives_differential

end CriticalBarrier.KernelPromotedG1Assembly
