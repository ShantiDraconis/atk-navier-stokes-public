import Mathlib

namespace NSThreeCaseClosure

inductive Bit where
  | false
  | true
  deriving DecidableEq, Repr

structure PairState where
  left : Bit
  right : Bit
  deriving DecidableEq, Repr

def admissible : PairState → Prop
  | ⟨.true, .true⟩ => False
  | _ => True

inductive ClosureMode where
  | falseTrue
  | trueFalse
  | falseFalse
  deriving DecidableEq, Repr

def modeOf (s : PairState) (h : admissible s) : ClosureMode :=
  match s with
  | ⟨.false, .true⟩ => .falseTrue
  | ⟨.true, .false⟩ => .trueFalse
  | ⟨.false, .false⟩ => .falseFalse
  | ⟨.true, .true⟩ => False.elim h

theorem true_true_excluded :
    ¬ admissible ⟨.true, .true⟩ := by
  simp [admissible]

theorem false_true_admissible :
    admissible ⟨.false, .true⟩ := by
  simp [admissible]

theorem true_false_admissible :
    admissible ⟨.true, .false⟩ := by
  simp [admissible]

theorem false_false_admissible :
    admissible ⟨.false, .false⟩ := by
  simp [admissible]

structure ClosureWitnesses (OpenMathClosed : Prop) where
  falseTrue : OpenMathClosed
  trueFalse : OpenMathClosed
  falseFalse : OpenMathClosed

theorem close_open_math_of_admissible
    {OpenMathClosed : Prop}
    (W : ClosureWitnesses OpenMathClosed)
    (s : PairState)
    (hs : admissible s) :
    OpenMathClosed := by
  cases s with
  | mk left right =>
      cases left <;> cases right
      · exact W.falseFalse
      · exact W.falseTrue
      · exact W.trueFalse
      · simp [admissible] at hs

structure TheoremEnablement where
  OpenMathClosed : Prop
  FinalTheorem : Prop
  closureWitnesses : ClosureWitnesses OpenMathClosed
  openMath_to_final : OpenMathClosed → FinalTheorem

theorem enable_final_theorem
    (E : TheoremEnablement)
    (s : PairState)
    (hs : admissible s) :
    E.FinalTheorem :=
  E.openMath_to_final
    (close_open_math_of_admissible E.closureWitnesses s hs)

#print axioms true_true_excluded
#print axioms close_open_math_of_admissible
#print axioms enable_final_theorem

end NSThreeCaseClosure
