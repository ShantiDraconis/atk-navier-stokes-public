import Mathlib
import open_math.RPA_MinimalChain

namespace RPA.EndpointLattice

structure FreeState where
  openCount : Nat
  closedCount : Nat
deriving DecidableEq, Repr

def emptyFree : FreeState := ⟨0, 0⟩
def openFree : FreeState := ⟨1, 0⟩
def closedFree : FreeState := ⟨0, 1⟩
def dualFree : FreeState := ⟨1, 1⟩

def addFree (a b : FreeState) : FreeState :=
  ⟨a.openCount + b.openCount, a.closedCount + b.closedCount⟩

instance : Add FreeState := ⟨addFree⟩

theorem open_plus_closed : openFree + closedFree = dualFree := rfl
theorem closed_plus_open : closedFree + openFree = dualFree := rfl
theorem open_plus_open : openFree + openFree = ⟨2, 0⟩ := rfl
theorem closed_plus_closed : closedFree + closedFree = ⟨0, 2⟩ := rfl
theorem two_open_one_closed : openFree + openFree + closedFree = ⟨2, 1⟩ := rfl
theorem one_open_two_closed : openFree + closedFree + closedFree = ⟨1, 2⟩ := rfl
theorem two_open_two_closed : openFree + openFree + closedFree + closedFree = ⟨2, 2⟩ := rfl

inductive Canonical where
  | empty
  | openOnly
  | closedOnly
  | full
deriving DecidableEq, Repr

def ofSupport (o c : Bool) : Canonical :=
  match o, c with
  | false, false => .empty
  | true, false => .openOnly
  | false, true => .closedOnly
  | true, true => .full

def canonicalize (s : FreeState) : Canonical :=
  ofSupport (s.openCount != 0) (s.closedCount != 0)

def hasOpen : Canonical → Bool
  | .empty => false
  | .openOnly => true
  | .closedOnly => false
  | .full => true

def hasClosed : Canonical → Bool
  | .empty => false
  | .openOnly => false
  | .closedOnly => true
  | .full => true

def join (a b : Canonical) : Canonical :=
  ofSupport (hasOpen a || hasOpen b) (hasClosed a || hasClosed b)

theorem canonical_empty : canonicalize emptyFree = .empty := rfl
theorem canonical_open : canonicalize openFree = .openOnly := rfl
theorem canonical_closed : canonicalize closedFree = .closedOnly := rfl
theorem canonical_dual : canonicalize dualFree = .full := rfl
theorem canonical_open_open : canonicalize (openFree + openFree) = .openOnly := rfl
theorem canonical_closed_closed : canonicalize (closedFree + closedFree) = .closedOnly := rfl
theorem canonical_closed_open : canonicalize (closedFree + openFree) = .full := rfl

theorem open_idempotent : join .openOnly .openOnly = .openOnly := rfl
theorem closed_idempotent : join .closedOnly .closedOnly = .closedOnly := rfl
theorem open_join_closed_full : join .openOnly .closedOnly = .full := rfl
theorem full_absorbs_left (x : Canonical) : join .full x = .full := by cases x <;> rfl
theorem full_absorbs_right (x : Canonical) : join x .full = .full := by cases x <;> rfl

def FULL (Open Closed : Prop) : Prop :=
  RPA.DUAL_ENDPOINT_STATE Open Closed

abbrev MATH (Open Closed : Prop) : Prop := FULL Open Closed
abbrev FINAL_ROOT (Open Closed : Prop) : Prop := FULL Open Closed
abbrev GLOBAL_EXTERNAL_CERTIFICATE (Open Closed : Prop) : Prop := FULL Open Closed

theorem full_eq_dual_endpoint_state (Open Closed : Prop) :
    FULL Open Closed ↔ RPA.DUAL_ENDPOINT_STATE Open Closed := Iff.rfl
theorem full_eq_math (Open Closed : Prop) :
    FULL Open Closed ↔ MATH Open Closed := Iff.rfl
theorem full_eq_final_root (Open Closed : Prop) :
    FULL Open Closed ↔ FINAL_ROOT Open Closed := Iff.rfl
theorem full_eq_global_external_certificate (Open Closed : Prop) :
    FULL Open Closed ↔ GLOBAL_EXTERNAL_CERTIFICATE Open Closed := Iff.rfl

theorem maximal_full_chain (Open Closed : Prop) :
    FULL Open Closed ↔
      RPA.DUAL_ENDPOINT_STATE Open Closed ∧
      MATH Open Closed ∧
      FINAL_ROOT Open Closed ∧
      GLOBAL_EXTERNAL_CERTIFICATE Open Closed := by
  constructor
  · intro h
    exact ⟨h, h, h, h⟩
  · rintro ⟨h, _, _, _⟩
    exact h

theorem open_open_open : openFree + openFree + openFree = ⟨3, 0⟩ := rfl
theorem closed_closed_closed : closedFree + closedFree + closedFree = ⟨0, 3⟩ := rfl
theorem open_open_closed : openFree + openFree + closedFree = ⟨2, 1⟩ := rfl
theorem open_closed_open : openFree + closedFree + openFree = ⟨2, 1⟩ := rfl
theorem closed_open_open : closedFree + openFree + openFree = ⟨2, 1⟩ := rfl
theorem open_closed_closed : openFree + closedFree + closedFree = ⟨1, 2⟩ := rfl
theorem closed_open_closed : closedFree + openFree + closedFree = ⟨1, 2⟩ := rfl
theorem closed_closed_open : closedFree + closedFree + openFree = ⟨1, 2⟩ := rfl

theorem canonical_open_open_open :
    canonicalize (openFree + openFree + openFree) = .openOnly := rfl
theorem canonical_closed_closed_closed :
    canonicalize (closedFree + closedFree + closedFree) = .closedOnly := rfl
theorem canonical_open_open_closed :
    canonicalize (openFree + openFree + closedFree) = .full := rfl
theorem canonical_open_closed_open :
    canonicalize (openFree + closedFree + openFree) = .full := rfl
theorem canonical_closed_open_open :
    canonicalize (closedFree + openFree + openFree) = .full := rfl
theorem canonical_open_closed_closed :
    canonicalize (openFree + closedFree + closedFree) = .full := rfl
theorem canonical_closed_open_closed :
    canonicalize (closedFree + openFree + closedFree) = .full := rfl
theorem canonical_closed_closed_open :
    canonicalize (closedFree + closedFree + openFree) = .full := rfl

def fullFree : FreeState :=
  openFree + openFree + closedFree + closedFree

theorem fullFree_counts : fullFree = ⟨2, 2⟩ := rfl
theorem canonical_fullFree : canonicalize fullFree = .full := rfl

structure CubeThroughThreeCertificate : Prop where
  open1 : canonicalize openFree = .openOnly
  closed1 : canonicalize closedFree = .closedOnly
  openClosed2 : canonicalize (openFree + closedFree) = .full
  closedOpen2 : canonicalize (closedFree + openFree) = .full
  openOpen2 : canonicalize (openFree + openFree) = .openOnly
  closedClosed2 : canonicalize (closedFree + closedFree) = .closedOnly
  openOpenOpen3 : canonicalize (openFree + openFree + openFree) = .openOnly
  closedClosedClosed3 : canonicalize (closedFree + closedFree + closedFree) = .closedOnly
  openOpenClosed3 : canonicalize (openFree + openFree + closedFree) = .full
  openClosedOpen3 : canonicalize (openFree + closedFree + openFree) = .full
  closedOpenOpen3 : canonicalize (closedFree + openFree + openFree) = .full
  openClosedClosed3 : canonicalize (openFree + closedFree + closedFree) = .full
  closedOpenClosed3 : canonicalize (closedFree + openFree + closedFree) = .full
  closedClosedOpen3 : canonicalize (closedFree + closedFree + openFree) = .full
  full22 : canonicalize fullFree = .full

def cubeThroughThreeCertificate : CubeThroughThreeCertificate where
  open1 := rfl
  closed1 := rfl
  openClosed2 := rfl
  closedOpen2 := rfl
  openOpen2 := rfl
  closedClosed2 := rfl
  openOpenOpen3 := rfl
  closedClosedClosed3 := rfl
  openOpenClosed3 := rfl
  openClosedOpen3 := rfl
  closedOpenOpen3 := rfl
  openClosedClosed3 := rfl
  closedOpenClosed3 := rfl
  closedClosedOpen3 := rfl
  full22 := rfl

theorem complete_cube_through_three :
    canonicalize openFree = .openOnly ∧
    canonicalize closedFree = .closedOnly ∧
    canonicalize (openFree + closedFree) = .full ∧
    canonicalize (closedFree + openFree) = .full ∧
    canonicalize (openFree + openFree) = .openOnly ∧
    canonicalize (closedFree + closedFree) = .closedOnly ∧
    canonicalize (openFree + openFree + openFree) = .openOnly ∧
    canonicalize (closedFree + closedFree + closedFree) = .closedOnly ∧
    canonicalize (openFree + openFree + closedFree) = .full ∧
    canonicalize (openFree + closedFree + openFree) = .full ∧
    canonicalize (closedFree + openFree + openFree) = .full ∧
    canonicalize (openFree + closedFree + closedFree) = .full ∧
    canonicalize (closedFree + openFree + closedFree) = .full ∧
    canonicalize (closedFree + closedFree + openFree) = .full ∧
    canonicalize fullFree = .full := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RPA.EndpointLattice
