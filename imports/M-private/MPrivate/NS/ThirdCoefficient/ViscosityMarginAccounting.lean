import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# ViscosityMarginAccounting

Every Young/absorption step spends part of the viscous term.  The signed route
is valid only if the sum of all absorbed fractions stays strictly below `nu`.
This file certifies the bookkeeping independently of the unresolved PDE bounds.
-/

/-- Total dissipative expenditure in the four-block route. -/
def totalEpsilon
    (epsGood epsLow epsCross epsAlign : ℝ) : ℝ :=
  epsGood + epsLow + epsCross + epsAlign

/-- Strict viscosity margin. -/
def HasViscosityMargin
    (epsGood epsLow epsCross epsAlign nu : ℝ) : Prop :=
  0 ≤ epsGood ∧ 0 ≤ epsLow ∧ 0 ≤ epsCross ∧ 0 ≤ epsAlign ∧
  totalEpsilon epsGood epsLow epsCross epsAlign < nu

/-- Full signed T3 assembly with every dissipative expenditure visible. -/
theorem assemble_T3_with_full_absorption_accounting
    (V Vgood Vlow Vcross Valign Z Y
      epsGood epsLow epsCross epsAlign
      C aLow aCross aAlign : ℝ)
    (hdec : V = Vgood + Vlow + Vcross + Valign)
    (hgood : Vgood ≤ epsGood * Z)
    (hlow : Vlow ≤ epsLow * Z + C * aLow * Y)
    (hcross : Vcross ≤ epsCross * Z + C * aCross * Y)
    (halign : Valign ≤ epsAlign * Z + C * aAlign * Y) :
    V ≤ totalEpsilon epsGood epsLow epsCross epsAlign * Z +
      C * (aLow + aCross + aAlign) * Y := by
  unfold totalEpsilon
  rw [hdec]
  nlinarith

/-- Exact balance plus a T3 estimate written with `epsTotal` leaves
`nu-epsTotal` units of dissipation. -/
theorem enstrophy_margin_from_total_absorption
    (yPrime nu Z V epsTotal aY : ℝ)
    (hbal : (1 / 2 : ℝ) * yPrime + nu * Z = V)
    (hT3 : V ≤ epsTotal * Z + aY) :
    (1 / 2 : ℝ) * yPrime + (nu - epsTotal) * Z ≤ aY := by
  linarith

/-- A strict viscosity margin gives a strictly positive surviving coefficient. -/
theorem surviving_viscosity_positive
    (epsGood epsLow epsCross epsAlign nu : ℝ)
    (h : HasViscosityMargin epsGood epsLow epsCross epsAlign nu) :
    0 < nu - totalEpsilon epsGood epsLow epsCross epsAlign := by
  unfold HasViscosityMargin at h
  linarith

/-- A strict viscosity margin itself forces positive viscosity. -/
theorem positive_viscosity_of_margin
    (epsGood epsLow epsCross epsAlign nu : ℝ)
    (h : HasViscosityMargin epsGood epsLow epsCross epsAlign nu) :
    0 < nu := by
  rcases h with ⟨hG, hL, hC, hA, hlt⟩
  have hsum : 0 ≤ totalEpsilon epsGood epsLow epsCross epsAlign := by
    unfold totalEpsilon
    positivity
  linarith

/-- Conversion to the normalized G1-flex parameter theta = epsTotal/nu. -/
noncomputable def thetaFromEpsilon (epsTotal nu : ℝ) : ℝ :=
  epsTotal / nu

/-- If `0 <= epsTotal < nu` and `nu>0`, then `theta` lies in `[0,1)`. -/
theorem thetaFromEpsilon_strict
    (epsTotal nu : ℝ)
    (heps0 : 0 ≤ epsTotal)
    (hnu : 0 < nu)
    (hlt : epsTotal < nu) :
    0 ≤ thetaFromEpsilon epsTotal nu ∧
    thetaFromEpsilon epsTotal nu < 1 := by
  unfold thetaFromEpsilon
  constructor
  · exact div_nonneg heps0 (le_of_lt hnu)
  · exact (div_lt_one hnu).2 hlt

/-- Audit obligations needed when this scalar accounting is embedded in the
actual Navier--Stokes scaling and time-dependent PDE argument. -/
structure ViscosityAccountingFrontier where
  viscosity_positive : Prop
  viscosity_scaling_convention_fixed : Prop
  epsilon_parameters_nonnegative : Prop
  epsilon_parameters_target_independent : Prop
  epsilon_parameters_future_independent : Prop
  total_margin_uniform_in_time : Prop
  total_margin_uniform_below_Tstar : Prop
  same_viscosity_used_in_energy_and_enstrophy : Prop
  no_hidden_viscosity_normalization_change : Prop
  no_endpoint_reuse : Prop

end MPrivate.NS.ThirdCoefficient
