import CriticalBarrier.ExternalFastPath

namespace CriticalBarrier.ExternalRouteRouter

/-- Canonical route identifiers. Legacy files remain preserved; only the
fast path is promoted for new closure work. -/
inductive Route
  | k1aCore
  | k1Analytic
  | g1Closure
  | globalClosure
  | finalExternal
  deriving DecidableEq, Repr

def next : Route → Option Route
  | .k1aCore => some .k1Analytic
  | .k1Analytic => some .g1Closure
  | .g1Closure => some .globalClosure
  | .globalClosure => some .finalExternal
  | .finalExternal => none

def rank : Route → Nat
  | .k1aCore => 0
  | .k1Analytic => 1
  | .g1Closure => 2
  | .globalClosure => 3
  | .finalExternal => 4

theorem next_strictly_advances {a b : Route} (h : next a = some b) :
    rank a < rank b := by
  cases a <;> simp [next, rank] at h ⊢
  all_goals subst_vars <;> decide

/-- No route can loop back to itself in one canonical transition. -/
theorem next_ne_self (a : Route) : next a ≠ some a := by
  intro h
  have := next_strictly_advances h
  exact (Nat.lt_irrefl _ this)

end CriticalBarrier.ExternalRouteRouter
