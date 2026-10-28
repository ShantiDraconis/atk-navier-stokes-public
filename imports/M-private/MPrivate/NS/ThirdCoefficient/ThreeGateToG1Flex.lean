import Mathlib
import MPrivate.NS.ThirdCoefficient.ViscosityMarginAccounting
import MPrivate.NS.ThirdCoefficient.G1FlexFromThirdCoefficient

namespace MPrivate.NS.ThirdCoefficient

/-!
# ThreeGateToG1Flex

Pure algebraic closure of the current three-gate PDE program.

Once the good/low/cross/alignment blocks satisfy pointwise estimates and all
viscosity expenditures remain below `nu`, the signed stretching bound has the
G1-flex form. No Navier--Stokes analytic bridge is proved here; this file only
removes all remaining assembly ambiguity.

Audit identity rule: the scalar assembly below is not itself evidence that its
inputs are the actual low/cross/alignment blocks of one Navier--Stokes solution.
A PDE use must separately certify identity continuity for all blocks, Y, Z,
viscosity, cutoff and interval.
-/

/-- Componentwise signed estimate package at one time. -/
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

/-- Exact decomposition plus the four pointwise block estimates. -/
def ThreeGatePointwiseCertified (d : ThreeGatePointwiseData) : Prop :=
  d.V = d.Vgood + d.Vlow + d.Vcross + d.Valign ∧
  d.Vgood ≤ d.epsGood * d.Z ∧
  d.Vlow ≤ d.epsLow * d.Z + d.C * d.aLow * d.Y ∧
  d.Vcross ≤ d.epsCross * d.Z + d.C * d.aCross * d.Y ∧
  d.Valign ≤ d.epsAlign * d.Z + d.C * d.aAlign * d.Y

/-- PDE-level identity continuity required before `ThreeGatePointwiseData` can be
used as the actual T3 package.  These are obligations, not consequences of the
scalar algebra. -/
structure ThreeGateIdentityContinuity where
  actual_solution_class_identified : Prop
  maximal_lifetime_is_actual_solution_lifetime : Prop
  same_solution_for_all_blocks : Prop
  same_time_for_all_blocks : Prop
  same_viscosity_for_all_absorption_terms : Prop
  same_cutoff_for_low_cross_alignment_where_applicable : Prop
  V_is_actual_signed_stretching : Prop
  Vgood_is_actual_good_block : Prop
  Vlow_is_actual_low_block : Prop
  Vcross_is_actual_cross_block : Prop
  Valign_is_actual_alignment_block : Prop
  Z_is_actual_enstrophy_dissipation : Prop
  Y_is_actual_enstrophy : Prop
  aLow_is_same_low_coefficient_used_in_T4 : Prop
  aCross_is_same_cross_coefficient_used_in_T4 : Prop
  aAlign_is_same_alignment_coefficient_used_in_T4 : Prop
  no_proxy_substitution : Prop
  no_scaling_identity_used_as_object_identification : Prop
  no_finite_truncation_used_as_infinite_object : Prop
  no_post_G1_result_used_upstream : Prop

/-- Total ThirdCoefficient at one time. -/
def pointwiseA3 (d : ThreeGatePointwiseData) : ℝ :=
  d.aLow + d.aCross + d.aAlign

/-- The block estimates assemble into one T3 estimate. -/
theorem three_gate_pointwise_assembles
    (d : ThreeGatePointwiseData)
    (h : ThreeGatePointwiseCertified d) :
    d.V ≤
      totalEpsilon d.epsGood d.epsLow d.epsCross d.epsAlign * d.Z +
      d.C * pointwiseA3 d * d.Y := by
  rcases h with ⟨hdec, hgood, hlow, hcross, halign⟩
  unfold pointwiseA3
  exact assemble_T3_with_full_absorption_accounting
    d.V d.Vgood d.Vlow d.Vcross d.Valign d.Z d.Y
    d.epsGood d.epsLow d.epsCross d.epsAlign
    d.C d.aLow d.aCross d.aAlign
    hdec hgood hlow hcross halign

/-- Convert total epsilon expenditure into the normalized G1-flex theta. -/
noncomputable def pointwiseTheta (d : ThreeGatePointwiseData) (nu : ℝ) : ℝ :=
  thetaFromEpsilon
    (totalEpsilon d.epsGood d.epsLow d.epsCross d.epsAlign) nu

/-- With positive viscosity and a strict total absorption margin, theta lies in
`[0,1)`. -/
theorem three_gate_theta_strict
    (d : ThreeGatePointwiseData)
    (nu : ℝ)
    (hmargin : HasViscosityMargin
      d.epsGood d.epsLow d.epsCross d.epsAlign nu) :
    0 ≤ pointwiseTheta d nu ∧ pointwiseTheta d nu < 1 := by
  unfold pointwiseTheta
  rcases hmargin with ⟨heG, heL, heC, heA, hlt⟩
  have hnu : 0 < nu := by
    have hsum0 : 0 ≤ totalEpsilon d.epsGood d.epsLow d.epsCross d.epsAlign := by
      unfold totalEpsilon
      positivity
    linarith
  have hsum0 : 0 ≤ totalEpsilon d.epsGood d.epsLow d.epsCross d.epsAlign := by
    unfold totalEpsilon
    positivity
  exact thetaFromEpsilon_strict
    (totalEpsilon d.epsGood d.epsLow d.epsCross d.epsAlign)
    nu hsum0 hnu hlt

/-- The assembled estimate is exactly a G1-flex estimate after absorbing the
constant `C` into the coefficient. -/
theorem three_gate_gives_G1flex
    (d : ThreeGatePointwiseData)
    (nu : ℝ)
    (hnu : 0 < nu)
    (h : ThreeGatePointwiseCertified d) :
    G1FlexEstimate
      d.V
      (pointwiseTheta d nu)
      nu
      d.Z
      (d.C * pointwiseA3 d)
      d.Y := by
  unfold G1FlexEstimate pointwiseTheta thetaFromEpsilon
  have hT3 := three_gate_pointwise_assembles d h
  have hnune : nu ≠ 0 := ne_of_gt hnu
  unfold totalEpsilon at hT3 ⊢
  field_simp [hnune]
  nlinarith

/-- Exact differential consequence once the actual enstrophy balance is also
supplied. -/
theorem three_gate_plus_balance_gives_differential
    (d : ThreeGatePointwiseData)
    (nu yPrime : ℝ)
    (hnu : 0 < nu)
    (hT3 : ThreeGatePointwiseCertified d)
    (hbal : EnstrophyBalance yPrime nu d.Z d.V) :
    (1 / 2 : ℝ) * yPrime +
      (1 - pointwiseTheta d nu) * nu * d.Z ≤
      (d.C * pointwiseA3 d) * d.Y := by
  have hg1 := three_gate_gives_G1flex d nu hnu hT3
  exact balance_and_G1flex_give_differential_inequality
    yPrime nu d.Z d.V (pointwiseTheta d nu)
    (d.C * pointwiseA3 d) d.Y hbal hg1

end MPrivate.NS.ThirdCoefficient
