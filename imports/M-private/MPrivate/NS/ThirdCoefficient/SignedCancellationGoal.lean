import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-- The active analytic target.  This is a proposition describing the obligation;
    no existence theorem for `a₃` is asserted here. -/
def SignedCancellationGoal
    (V Z a Y ε K : ℝ) : Prop :=
  V ≤ ε * Z + K * a * Y

/-- Internal guardrails preserving cancellation during an attempted proof. -/
structure SignedCancellationProtocol where
  replacedSignedByPositiveEarly : Bool
  replacedSignedByAbsEarly : Bool
  usesCircularBudget : Bool
  deriving DecidableEq, Repr

def SignedCancellationProtocol.clean (P : SignedCancellationProtocol) : Bool :=
  !(P.replacedSignedByPositiveEarly ||
    P.replacedSignedByAbsEarly ||
    P.usesCircularBudget)

/-- SC1--SC3 all pass only when the proof path has preserved the signed object
    and has not imported a circular budget. -/
example : SignedCancellationProtocol.clean
    { replacedSignedByPositiveEarly := false
      replacedSignedByAbsEarly := false
      usesCircularBudget := false } = true := by
  rfl

/-- Replacing the signed term by its absolute value before testing cancellation
    is explicitly rejected by the protocol. -/
example : SignedCancellationProtocol.clean
    { replacedSignedByPositiveEarly := false
      replacedSignedByAbsEarly := true
      usesCircularBudget := false } = false := by
  rfl

end MPrivate.NS.ThirdCoefficient
