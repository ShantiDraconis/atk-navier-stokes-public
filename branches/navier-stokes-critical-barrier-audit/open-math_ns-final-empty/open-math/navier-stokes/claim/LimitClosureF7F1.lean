import Mathlib

namespace NSLimitClosureF7F1

open Filter Topology

variable {State : Type} [TopologicalSpace State]

inductive Stage where
  | C0
  | O
  | C2
  deriving DecidableEq, Repr

structure MultistateResidualNumber where
  approxValue : ℕ → ℝ
  limitValue : ℝ
  c0Value : ℝ

def ResidualVanishes (R : MultistateResidualNumber) : Prop :=
  Tendsto R.approxValue atTop (nhds R.limitValue) ∧ R.limitValue = 0

structure ApproximatingLane where
  u : ℕ → State
  limit : State
  residual : MultistateResidualNumber

structure CompactnessCertificate (A : ApproximatingLane (State := State)) where
  converges : Tendsto A.u atTop (nhds A.limit)
  uniqueLimit :
    ∀ v : State, Tendsto A.u atTop (nhds v) → v = A.limit

structure ClosedPropertyCertificate
    (P : State → Prop) (A : ApproximatingLane (State := State)) where
  passes_to_limit :
    (∀ n, P (A.u n)) →
    Tendsto A.u atTop (nhds A.limit) →
    ResidualVanishes A.residual →
    P A.limit

structure RegularityCertificate
    (P GlobalSmooth : State → Prop) where
  closes : ∀ u, P u → GlobalSmooth u

structure LimitClosureCertificate
    (P : State → Prop)
    (A : ApproximatingLane (State := State)) where
  approximants_green : ∀ n, P (A.u n)
  compactness : CompactnessCertificate A
  residual_vanishing : ResidualVanishes A.residual
  closed_property : ClosedPropertyCertificate P A

theorem limit_property_closure
    (P : State → Prop)
    (A : ApproximatingLane (State := State))
    (C : LimitClosureCertificate P A) :
    P A.limit := by
  exact C.closed_property.passes_to_limit
    C.approximants_green
    C.compactness.converges
    C.residual_vanishing

theorem navier_stokes_limit_closure
    (P GlobalSmooth : State → Prop)
    (A : ApproximatingLane (State := State))
    (C : LimitClosureCertificate P A)
    (R : RegularityCertificate P GlobalSmooth) :
    GlobalSmooth A.limit :=
  R.closes A.limit (limit_property_closure P A C)

def OpenMathProducer
    (P : State → Prop)
    (A : ApproximatingLane (State := State)) : Prop :=
  Nonempty (LimitClosureCertificate P A)

theorem open_math_producer_enables_theorem
    (P GlobalSmooth : State → Prop)
    (A : ApproximatingLane (State := State))
    (hOpen : OpenMathProducer P A)
    (R : RegularityCertificate P GlobalSmooth) :
    GlobalSmooth A.limit := by
  rcases hOpen with ⟨C⟩
  exact navier_stokes_limit_closure P GlobalSmooth A C R

theorem exact_material_gap
    (P : State → Prop)
    (A : ApproximatingLane (State := State)) :
    OpenMathProducer P A ↔ Nonempty (LimitClosureCertificate P A) := by
  rfl

#print axioms limit_property_closure
#print axioms navier_stokes_limit_closure
#print axioms open_math_producer_enables_theorem
#print axioms exact_material_gap

end NSLimitClosureF7F1
