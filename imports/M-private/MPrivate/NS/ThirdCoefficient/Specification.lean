import Mathlib

namespace MPrivate.NS.ThirdCoefficient

-- Abstract solution/state type used by the adversarial classifier.
-- No Navier--Stokes existence statement is encoded here.
variable {State : Type*}

/-- Data needed to state, but not assume, a ThirdCoefficient candidate. -/
structure Candidate (State : Type*) where
  scale : ℝ → State → State
  a : State → ℝ → ℝ
  Y : State → ℝ → ℝ
  Z : State → ℝ → ℝ
  V : State → ℝ → ℝ
  initialBudget : State → ℝ

/-- T1: pointwise nonnegativity. -/
def T1Nonnegative (C : Candidate State) : Prop :=
  ∀ u t, 0 ≤ C.a u t

/-- T2: critical coefficient scaling. -/
def T2CriticalScaling (C : Candidate State) : Prop :=
  ∀ u t lambda, 0 < lambda →
    C.a (C.scale lambda u) t =
      lambda ^ 2 * C.a u (lambda ^ 2 * t)

/-- T3: stretching can be absorbed by dissipation plus `a Y`.
    Constants are explicit inputs; this definition does not assert existence. -/
def T3DominatesStretching (C : Candidate State) (ε K : ℝ) : Prop :=
  0 < ε ∧ 0 ≤ K ∧
  ∀ u t, C.V u t ≤ ε * C.Z u t + K * C.a u t * C.Y u t

/-- T4: a non-circular time-integral budget.  The integral implementation is
    deliberately external to this pure interface. -/
def T4EnergyControlled
    (timeIntegral : (ℝ → ℝ) → ℝ → ℝ)
    (C : Candidate State) : Prop :=
  ∀ u T, timeIntegral (C.a u) T ≤ C.initialBudget u

/-- T5: marker predicate for a budget that does not depend on `sup Y`.
    The concrete dependency audit belongs to each candidate module. -/
def T5NoSupY (budgetDependsOnSupY : Prop) : Prop := ¬ budgetDependsOnSupY

/-- T6: marker predicate excluding a `Z/Y` construction. -/
def T6NoZDivY (usesZDivY : Prop) : Prop := ¬ usesZDivY

/-- T7: marker predicate excluding BKM/Ladyzhenskaya--Prodi--Serrin-equivalent
    assumptions from the budget. -/
def T7NoContinuationCriterion (usesContinuationCriterion : Prop) : Prop :=
  ¬ usesContinuationCriterion

/-- T8: marker predicate excluding uncontrolled higher derivatives. -/
def T8NoUncontrolledHigherDerivative (usesHigherDerivative : Prop) : Prop :=
  ¬ usesHigherDerivative

/-- T9: compatibility with the Leray energy layer is candidate-specific. -/
def T9LerayCompatible (p : Prop) : Prop := p

/-- T10: Navier--Stokes scaling compatibility. -/
def T10ScalingCompatible (C : Candidate State) : Prop := T2CriticalScaling C

/-- T11: no use of the desired global conclusion. -/
def T11NoConclusionReuse (usesGlobalConclusion : Prop) : Prop :=
  ¬ usesGlobalConclusion

/-- T12 is a repository/CI certificate: zero `sorry`/`admit`/new axioms and a
    clean `#print axioms` audit.  It is intentionally not encoded as a
    mathematical proposition that could simply be assumed. -/
inductive FormalAuditStatus where
  | pending
  | passed
  | failed
  deriving DecidableEq, Repr

/-- Eight ledger statuses used by the project. -/
inductive LedgerStatus where
  | formalProved
  | formalRefuted
  | conditionalProved
  | classicalImported
  | numericallyVerified
  | open
  | releaseCandidate
  | independentlyVerified
  deriving DecidableEq, Repr

end MPrivate.NS.ThirdCoefficient
