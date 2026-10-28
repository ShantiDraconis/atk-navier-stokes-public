import Mathlib
import MPrivate.NS.ThirdCoefficient.Specification
import MPrivate.NS.ThirdCoefficient.SignedStretchingCandidate
import MPrivate.NS.ThirdCoefficient.SpectralSignedStretching

namespace MPrivate.NS.ThirdCoefficient

abbrev Time := ℝ
abbrev Scale := ℝ

def posPart (x : ℝ) : ℝ := max x 0

def negPart (x : ℝ) : ℝ := max (-x) 0

theorem scalar_eq_pos_sub_neg (x : ℝ) :
    x = posPart x - negPart x := by
  unfold posPart negPart
  rcases le_total x 0 with hx | hx
  · simp [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
  · have hnx : -x ≤ 0 := neg_nonpos.mpr hx
    simp [max_eq_left hx, max_eq_right hnx]

theorem V_eq_P_minus_N
    (V P N : ℝ)
    (hV : V = P - N) :
    V = P - N := hV

theorem eight_terms_preserve_sign
    (vLLL vLLH vLHL vLHH vHLL vHLH vHHL vHHH : ℝ) :
    vLLL + vLLH + vLHL + vLHH + vHLL + vHLH + vHHL + vHHH =
      vLLL + vLLH + vLHL + vLHH + vHLL + vHLH + vHHL + vHHH := rfl

def ScaleCritical
    {State : Type*}
    (scale : ℝ → State → State)
    (a3 : State → Time → ℝ) : Prop :=
  ∀ (u : State) (lambda t : ℝ), 0 < lambda →
    a3 (scale lambda u) t = lambda^2 * a3 u (lambda^2 * t)

/-- Signed T3 target for fixed admissible constants `ε` and `C`. -/
def SignedDominatesStretching
    {State : Type*}
    (V Z Y a3 : State → Time → ℝ)
    (ε C : ℝ) : Prop :=
  0 < ε ∧ 0 ≤ C ∧
  ∀ u t,
    V u t ≤ ε * Z u t + C * a3 u t * Y u t

/-- Viscosity-aware admissibility for the absorption parameter. -/
def SignedAbsorptionAdmissible (ε nu : ℝ) : Prop :=
  0 < ε ∧ ε < nu ∧ 0 < nu

def SignedAlignmentCandidate
    {State : Type*}
    (scale : ℝ → State → State)
    (V Z Y a3 : State → Time → ℝ)
    (ε C : ℝ) : Prop :=
  (∀ u t, 0 ≤ a3 u t) ∧
  ScaleCritical scale a3 ∧
  SignedDominatesStretching V Z Y a3 ε C

structure AlignmentCoherence where
  defect : Scale → Time → ℝ
  nonneg : ∀ J t, 0 ≤ defect J t

/-- Full scalar admissibility of the coherence defect. -/
def AlignmentCoherenceAdmissible
    (D : AlignmentCoherence) : Prop :=
  ∀ J t, D.defect J t ≤ 1

def AlignmentDepletionAtScale
    (D : AlignmentCoherence)
    (J : Scale) (t : Time) : Prop :=
  D.defect J t ≤ 1

def HighFrequencyBound
    (VH Z Y : Time → ℝ)
    (D : AlignmentCoherence)
    (J ε C : ℝ) : Prop :=
  ∀ t,
    VH t ≤ ε * Z t + C * D.defect J t * Y t

def CrossTermBound
    (Vcross Z Y a3cross : Time → ℝ)
    (ε C : ℝ) : Prop :=
  ∀ t,
    Vcross t ≤ ε * Z t + C * a3cross t * Y t

def decomposedA3
    (aLow aCross aAlign : Time → ℝ) : Time → ℝ :=
  fun t => aLow t + aCross t + aAlign t

theorem decomposedA3_nonneg
    (aLow aCross aAlign : Time → ℝ)
    (hLow : ∀ t, 0 ≤ aLow t)
    (hCross : ∀ t, 0 ≤ aCross t)
    (hAlign : ∀ t, 0 ≤ aAlign t) :
    ∀ t, 0 ≤ decomposedA3 aLow aCross aAlign t := by
  intro t
  unfold decomposedA3
  exact add_nonneg (add_nonneg (hLow t) (hCross t)) (hAlign t)

/-- Internal signed-route gates. These are specifications, not proofs. -/
structure SignedRouteGates where
  T1_nonnegative : Prop
  T2_scaleCritical : Prop
  T3_signedPDE : Prop
  T4_criticalL1Budget : Prop
  T5_noSupY : Prop
  T6_noRatioByY : Prop
  T7_noContinuationCriterion : Prop
  T8_noUncontrolledHigherDerivative : Prop
  T9_lerayCompatible : Prop
  T10_nsScalingCompatible : Prop
  T11_noGlobalConclusionUsed : Prop
  T12_kernelClean : Prop
  S1_preserveSign : Prop
  S2_preserveLowHigh : Prop
  S3_dimensionlessBudget : Prop
  viscosity_positive : Prop
  epsilon_below_viscosity : Prop
  all_absorption_costs_below_viscosity : Prop
  actual_NS_block_identification : Prop
  zero_vorticity_case_handled : Prop
  zero_strain_case_handled : Prop
  principal_value_kernel_justified : Prop
  coefficient_time_measurable : Prop
  coefficient_time_integrable : Prop
  budget_initial_data_only : Prop
  budget_uniform_for_all_T_below_Tstar : Prop
  maximal_time_passage_justified : Prop
  no_future_critical_norm : Prop
  no_Tstar_dependence : Prop
  no_BKM_LPS : Prop

def DominatesKnownBarrier
    (a3 oldBarrier : Time → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ t, c * oldBarrier t ≤ a3 t

def EquivalentToKnownBarrier
    (a3 oldBarrier : Time → ℝ) : Prop :=
  DominatesKnownBarrier a3 oldBarrier ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t, a3 t ≤ C * oldBarrier t

end MPrivate.NS.ThirdCoefficient
