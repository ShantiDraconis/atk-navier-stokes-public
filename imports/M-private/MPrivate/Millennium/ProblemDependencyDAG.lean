import Mathlib
import MPrivate.Millennium.YangMillsFrontier
import MPrivate.Millennium.HodgeFrontier
import MPrivate.Millennium.RHFrontier
import MPrivate.Millennium.BSDFrontier
import MPrivate.Millennium.PvsNPFrontier

namespace MPrivate.Millennium

/-!
# ProblemDependencyDAG

Cross-problem audit register. The six problems do not share one literal energy
inequality. They share only a workflow discipline: isolate the native decisive
bridge, keep downstream logic conditional, and record invalid shortcuts.
-/

inductive NativeProblem where
  | NavierStokes
  | YangMills
  | Hodge
  | RiemannHypothesis
  | BSD
  | PvsNP
  deriving DecidableEq, Repr

inductive GateStatus where
  | provedLogic
  | formalRefutedRoute
  | openBridge
  | externalPending
  | conditional
  | notEstablished
  deriving DecidableEq, Repr

structure NativeGate where
  problem : NativeProblem
  name : String
  status : GateStatus
  dependencies : List String
  note : String
  deriving Repr

/-- Current decisive gates only. -/
def decisiveGates : List NativeGate := [
  { problem := .NavierStokes,
    name := "ActualNS_to_G1flex",
    status := .openBridge,
    dependencies := ["LOW", "CROSS", "ALIGN", "T4 non-circular L1 budget"],
    note := "signed vortex-stretching bridge" },
  { problem := .YangMills,
    name := "construct_4D_QFT_and_positive_gap",
    status := .openBridge,
    dependencies := ["OS-compatible continuum construction", "Hamiltonian reconstruction", "spectral gap"],
    note := "existence and gap are separate native obligations" },
  { problem := .Hodge,
    name := "rational_Hodge_class_to_algebraic_cycle",
    status := .openBridge,
    dependencies := ["geometric projector or other native algebraicity mechanism"],
    note := "idempotence alone is insufficient" },
  { problem := .RiemannHypothesis,
    name := "native_analytic_identity_to_critical_line",
    status := .openBridge,
    dependencies := ["zero-independent functional", "coercive off-line control", "integrable error"],
    note := "artificial Gronwall variables alone have no RH content" },
  { problem := .BSD,
    name := "analytic_order_and_leading_term_arithmetic",
    status := .openBridge,
    dependencies := ["order=rank", "leading coefficient formula", "required finiteness statements"],
    note := "rank equality does not imply leading formula" },
  { problem := .PvsNP,
    name := "unconditional_superpolynomial_lower_bound",
    status := .openBridge,
    dependencies := ["explicit lower bound in fixed model", "barrier analysis"],
    note := "barrier escape is not itself a lower bound" }
]

/-- Universal audit rule used across problems. -/
structure NoOverclaimRule where
  theoremNameNoStrongerThanConclusion : Prop
  noOpenBridgePromotedToTheorem : Prop
  noFiniteComputationPromotedToUniversalProof : Prop
  noExternalTheoremWithoutHypothesisMap : Prop
  noConclusionReusedAsInput : Prop

/-- Current global status: all six decisive native bridges remain open. -/
def allSixRemainOpen : Prop :=
  ∀ g ∈ decisiveGates, g.status = .openBridge

theorem decisiveGates_all_open : allSixRemainOpen := by
  intro g hg
  simp [decisiveGates] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end MPrivate.Millennium
