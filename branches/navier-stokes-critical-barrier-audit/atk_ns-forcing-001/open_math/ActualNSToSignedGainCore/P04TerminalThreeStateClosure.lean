import Mathlib

/-!
NS terminal three-state closure probe.

This module formalizes only the finite closure pattern requested for the
terminal frontier: a closed left state and a closed right state both map to
the same middle/core state. The finite code has exactly three states 0,1,2.

This is an abstract closure invariant. It is intentionally separated from the
Navier--Stokes PDE endpoint so the kernel can decide what this structure
actually implies without smuggling in a material PDE proof.
-/

namespace NSProducerFirst.TerminalThreeStateClosure

inductive State
  | left
  | core
  | right
  deriving DecidableEq, Repr

def code : State → Fin 3
  | .left => 0
  | .core => 1
  | .right => 2

theorem code_left : code .left = 0 := rfl
theorem code_core : code .core = 1 := rfl
theorem code_right : code .right = 2 := rfl

/-- Both closed extremal states collapse to the same core in one step. -/
def collapse : State → State
  | .left => .core
  | .core => .core
  | .right => .core

@[simp] theorem collapse_left : collapse .left = .core := rfl
@[simp] theorem collapse_core : collapse .core = .core := rfl
@[simp] theorem collapse_right : collapse .right = .core := rfl

/-- The core is a fixed point of the closure map. -/
theorem core_fixed : collapse .core = .core := rfl

/-- Every state reaches the same core after one closure step. -/
theorem all_collapse_to_core (s : State) :
    collapse s = .core := by
  cases s <;> rfl

/-- Reapplying closure after reaching the core adds no information. -/
theorem collapse_idempotent (s : State) :
    collapse (collapse s) = collapse s := by
  cases s <;> rfl

/-- The left and right closed fronts meet at the same core. -/
theorem bilateral_meet :
    collapse .left = collapse .right := by
  rfl

/-- Finite three-state closure is consistent and nonempty. -/
theorem three_state_model_exists :
    Nonempty State := ⟨.core⟩

/-- Negative control: this closure structure alone cannot prove an arbitrary
proposition; instantiate the proposition with False. -/
theorem closure_does_not_create_arbitrary_endpoint :
    ¬ (∀ P : Prop, P) := by
  intro h
  exact h False


/-! ### Last-bit normalization -/

/-- A two-coordinate terminal code over the three finite states. -/
abbrev PairCode := Fin 3 × Fin 3

/-- Normalize a mixed last-bit code to the diagonal selected by its second
coordinate. This captures 0/1 -> 1/1 and 0/2 -> 2/2 exactly. -/
def normalizeLastBit : PairCode → PairCode
  | (_, j) => (j, j)

@[simp] theorem normalize_01 :
    normalizeLastBit (0, 1) = (1, 1) := rfl

@[simp] theorem normalize_02 :
    normalizeLastBit (0, 2) = (2, 2) := rfl

@[simp] theorem normalize_00 :
    normalizeLastBit (0, 0) = (0, 0) := rfl

/-- Every normalized terminal code lies on the diagonal. -/
theorem normalize_is_diagonal (p : PairCode) :
    (normalizeLastBit p).1 = (normalizeLastBit p).2 := by
  cases p
  rfl

/-- Once a terminal code reaches the diagonal, normalization is stable. -/
theorem normalize_idempotent (p : PairCode) :
    normalizeLastBit (normalizeLastBit p) = normalizeLastBit p := by
  cases p
  rfl

/-- The three diagonal states are exactly the fixed points of last-bit
normalization. -/
theorem normalize_fixed_iff_diagonal (p : PairCode) :
    normalizeLastBit p = p ↔ p.1 = p.2 := by
  rcases p with ⟨i, j⟩
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

/-- The normalization law itself remains a finite structural invariant; it
does not select truth or falsity for an unrelated proposition. -/
theorem last_bit_normalization_does_not_decide_arbitrary_prop :
    ¬ (∀ P : Prop, P ∨ ¬ P → P) := by
  intro h
  have hf : False ∨ ¬ False := Or.inr not_false
  exact h False hf

end NSProducerFirst.TerminalThreeStateClosure
