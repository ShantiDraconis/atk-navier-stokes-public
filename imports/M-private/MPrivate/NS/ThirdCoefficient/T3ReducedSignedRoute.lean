import Mathlib
import MPrivate.NS.ThirdCoefficient.T3SignedAssembly
import MPrivate.NS.ThirdCoefficient.LowFrequencyAbsorptionAlternative
import MPrivate.NS.ThirdCoefficient.CrossTermYoungAbsorption
import MPrivate.NS.ThirdCoefficient.AlignmentDefectFactorization

namespace MPrivate.NS.ThirdCoefficient

/-!
# T3ReducedSignedRoute

This file contains only a CONDITIONAL reduced T3 algebra: if an independently
certified low-frequency estimate really absorbs `Vlow` into dissipation, then
the temporal coefficient may be reduced to cross + alignment.

It must not be read as a proof of low-frequency absorption on `ℝ³`.  In
particular, the rejected reverse-Poincare step for a low-pass function is not an
admissible source of `LowDirectAbsorption`.  The generic `ℝ³` low route remains
open unless a different, rigorously certified estimate is supplied.
-/

/-- Reduced signed decomposition with the low block still visible algebraically. -/
def ReducedSignedDecomposition
    (V Vgood Vlow Vcross Valign : ℝ) : Prop :=
  V = Vgood + Vlow + Vcross + Valign

/-- Total dissipation fraction used by the good and conditionally absorbed low blocks. -/
def totalAbsorption (epsGood epsLow : ℝ) : ℝ := epsGood + epsLow

/-- Conditional algebra: if good and low blocks are already absorbed and the
other two factor through `Y`, then T3 needs only `aCross + aAlign`.
This theorem does not prove `LowDirectAbsorption`. -/
theorem assemble_reduced_signed_T3
    (V Vgood Vlow Vcross Valign Z Y
      epsGood epsLow C aCross aAlign : ℝ)
    (hdec : ReducedSignedDecomposition V Vgood Vlow Vcross Valign)
    (hgood : Vgood ≤ epsGood * Z)
    (hlow : LowDirectAbsorption Vlow epsLow Z)
    (hcross : Vcross ≤ C * aCross * Y)
    (halign : Valign ≤ C * aAlign * Y) :
    V ≤ totalAbsorption epsGood epsLow * Z +
      C * (aCross + aAlign) * Y := by
  unfold ReducedSignedDecomposition at hdec
  unfold LowDirectAbsorption at hlow
  unfold totalAbsorption
  rw [hdec]
  nlinarith

/-- The strict G1-flex dissipative margin survives when the total absorbed
fraction is strictly smaller than viscosity. -/
theorem reduced_route_strict_margin
    (epsGood epsLow nu : ℝ)
    (h : AbsorptionBudgetAdmissible (totalAbsorption epsGood epsLow) nu) :
    totalAbsorption epsGood epsLow < nu := by
  exact h.2

/-- Conditional reduced coefficient.  This definition is admissible only after
low elimination has been separately certified. -/
def reducedA3
    (aCross aAlign : ℝ → ℝ) : ℝ → ℝ :=
  fun t => aCross t + aAlign t

/-- Nonnegative cross/alignment pieces give a nonnegative conditional reduced coefficient. -/
theorem reducedA3_nonneg
    (aCross aAlign : ℝ → ℝ)
    (hCross : ∀ t, 0 ≤ aCross t)
    (hAlign : ∀ t, 0 ≤ aAlign t) :
    ∀ t, 0 ≤ reducedA3 aCross aAlign t := by
  intro t
  unfold reducedA3
  exact add_nonneg (hCross t) (hAlign t)

/-- Audit gate for using the reduced route.  The low block may be eliminated
only by a separately certified estimate; reverse Poincare for a generic
low-pass function on `ℝ³` is explicitly excluded. -/
structure ReducedRouteAdmissibility where
  low_elimination_certified : Prop
  low_estimate_valid_on_domain : Prop
  no_reverse_low_pass_poincare : Prop
  low_constant_target_independent : Prop
  low_constant_time_independent : Prop
  strict_viscosity_margin : Prop

/-- Remaining analytic content for the conditional reduced route. -/
structure ReducedT3Frontier where
  actualNS_decomposition : Prop
  good_absorption : Prop
  reduced_route_admissible : ReducedRouteAdmissibility
  cross_young_representation : Prop
  cross_remainder_factorization : Prop
  alignment_signed_factorization : Prop
  no_supY : Prop
  no_Z_div_Y : Prop
  no_BKM_LPS : Prop
  no_higher_derivative : Prop

end MPrivate.NS.ThirdCoefficient
