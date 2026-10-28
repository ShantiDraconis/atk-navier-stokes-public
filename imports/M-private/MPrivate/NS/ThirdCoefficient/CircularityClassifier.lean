import Mathlib

namespace MPrivate.NS.ThirdCoefficient

structure DependencyFlags where
  usesSupY : Bool
  usesZDivY : Bool
  usesContinuationCriterion : Bool
  usesHigherDerivative : Bool
  usesGlobalConclusion : Bool
  deriving DecidableEq, Repr

def DependencyFlags.clean (d : DependencyFlags) : Bool :=
  !(d.usesSupY || d.usesZDivY || d.usesContinuationCriterion ||
    d.usesHigherDerivative || d.usesGlobalConclusion)

example :
    DependencyFlags.clean
      { usesSupY := false
        usesZDivY := false
        usesContinuationCriterion := false
        usesHigherDerivative := false
        usesGlobalConclusion := false } = true := by
  rfl

example :
    DependencyFlags.clean
      { usesSupY := false
        usesZDivY := true
        usesContinuationCriterion := false
        usesHigherDerivative := false
        usesGlobalConclusion := false } = false := by
  rfl

end MPrivate.NS.ThirdCoefficient
