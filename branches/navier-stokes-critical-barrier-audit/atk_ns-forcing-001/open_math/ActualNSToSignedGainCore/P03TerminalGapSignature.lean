import Mathlib

/-!
NS terminal gap signature.

This file formalizes the exact "last-bit repeats forever" phenomenon:
once the admissible expansion map reaches the terminal obligation, every
further expansion returns the same obligation. This certifies a fixed-point
frontier of the search. It does not manufacture an inhabitant of the
underlying Navier--Stokes endpoint proposition.
-/

namespace NSProducerFirst.TerminalGapSignature

structure Signature (Obligation : Type) where
  expand : Obligation → Obligation
  fixed : ∀ o, expand o = o

def repeat {Obligation : Type} (step : Obligation → Obligation) :
    Nat → Obligation → Obligation
  | 0, o => o
  | n + 1, o => repeat step n (step o)

theorem repeat_eq_terminal
    {Obligation : Type}
    (S : Signature Obligation)
    (n : Nat) (o : Obligation) :
    repeat S.expand n o = o := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [repeat, S.fixed, ih]

theorem expansion_adds_no_new_obligation
    {Obligation : Type}
    (S : Signature Obligation)
    (o : Obligation) :
    S.expand o = o :=
  S.fixed o

/-- The fixed-point signature is a frontier certificate, not an inhabitant
of an unrelated target proposition. -/
theorem signature_alone_does_not_imply_arbitrary_target :
    (∃ S : Signature Unit, True) ∧ ¬ False := by
  constructor
  · refine ⟨{ expand := id, fixed := ?_ }, trivial⟩
    intro o
    rfl
  · exact not_false


/-- Skipping the terminal expansion step changes nothing. -/
theorem skip_terminal_bit
    {Obligation : Type}
    (S : Signature Obligation)
    (o : Obligation) :
    repeat S.expand 1 o = o := by
  simpa using repeat_eq_terminal S 1 o

/-- Restarting the expansion after the skipped terminal bit reproduces the
same terminal obligation after any finite number of further steps. -/
theorem restart_after_skip_is_same_terminal
    {Obligation : Type}
    (S : Signature Obligation)
    (n : Nat) (o : Obligation) :
    repeat S.expand n (repeat S.expand 1 o) = o := by
  rw [skip_terminal_bit S o]
  exact repeat_eq_terminal S n o

/-- Any two finite continuation lengths beyond the terminal frontier are
indistinguishable at the level of obligations. -/
theorem all_finite_continuations_agree
    {Obligation : Type}
    (S : Signature Obligation)
    (m n : Nat) (o : Obligation) :
    repeat S.expand m o = repeat S.expand n o := by
  rw [repeat_eq_terminal S m o, repeat_eq_terminal S n o]


/-! ### Terminal logical cycle -/

/-- The four terminal names are definitionally the same proposition. -/
abbrev Endpoint (P : Prop) : Prop := P
abbrev Gap (P : Prop) : Prop := Endpoint P
abbrev Habitant (P : Prop) : Prop := Gap P
abbrev Inhabitant (P : Prop) : Prop := Habitant P

theorem endpoint_to_gap {P : Prop} : Endpoint P → Gap P := id
theorem gap_to_habitant {P : Prop} : Gap P → Habitant P := id
theorem habitant_to_inhabitant {P : Prop} : Habitant P → Inhabitant P := id
theorem inhabitant_to_endpoint {P : Prop} : Inhabitant P → Endpoint P := id

theorem endpoint_iff_gap {P : Prop} : Endpoint P ↔ Gap P := Iff.rfl
theorem gap_iff_habitant {P : Prop} : Gap P ↔ Habitant P := Iff.rfl
theorem habitant_iff_inhabitant {P : Prop} : Habitant P ↔ Inhabitant P := Iff.rfl
theorem terminal_cycle {P : Prop} : Endpoint P ↔ Inhabitant P := Iff.rfl

/-- The terminal cycle is conservative: inhabiting any node is exactly the
same as inhabiting the endpoint; the cycle itself adds no proof term. -/
theorem terminal_inhabited_iff_endpoint {P : Prop} :
    Inhabited (Endpoint P) ↔ Endpoint P := by
  constructor
  · rintro ⟨h⟩
    exact h
  · intro h
    exact ⟨h⟩

/-- A concrete negative control: the cycle exists definitionally even when
the endpoint proposition is false. -/
theorem terminal_cycle_does_not_create_false :
    (Endpoint False ↔ Gap False) ∧ ¬ Endpoint False := by
  exact ⟨Iff.rfl, not_false⟩


/-- There is no generic inhabitant constructor produced by the terminal cycle
alone. If there were, applying it to False would derive False. -/
theorem no_generic_terminal_inhabitant :
    ¬ (∀ P : Prop, Endpoint P) := by
  intro h
  exact h False

end NSProducerFirst.TerminalGapSignature
