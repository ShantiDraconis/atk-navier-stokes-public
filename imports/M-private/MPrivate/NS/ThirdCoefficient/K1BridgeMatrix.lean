import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# K1BridgeMatrix

The six historical K1 obligations from the frozen audit are not an independent
proof stack; each feeds a concrete part of the current ThirdCoefficient route.
This typed matrix records those dependencies so that closing one K1 item cannot
be mistaken for closing G1-flex.
-/

inductive K1Obligation where
  | K1a_commutatorDerivation
  | K1b_transportGradient
  | K1c_nearFarBiotSavart
  | K1d_uniformStrictGamma
  | K1e_epsilonLimit
  | K1f_effectiveVolumeNormalization
  | tightness
  deriving DecidableEq, Repr

inductive CurrentGate where
  | spectralToEvolutionAssignment
  | crossFactorization
  | alignmentFactorization
  | exceptionalTail
  | viscosityMargin
  | actualNSLimitPassage
  | measurabilityAndIntegrability
  | maximalTimePassage
  | cutoffNonCircularity
  | noHiddenEndpointNorm
  | L1Budget
  deriving DecidableEq, Repr

/-- Human-auditable dependency row. `statusOpen` is metadata only; it is not a
proof object and must never be used as evidence that a gate is discharged. -/
structure K1GateDependency where
  obligation : K1Obligation
  feeds : List CurrentGate
  statusOpen : Bool
  note : String
  deriving Repr

/-- Canonical dependency map for the current route. -/
def k1BridgeMatrix : List K1GateDependency := [
  { obligation := .K1a_commutatorDerivation,
    feeds := [.spectralToEvolutionAssignment, .crossFactorization, .measurabilityAndIntegrability],
    statusOpen := true,
    note := "derives orientation/strain evolution and commutator costs; analytic regularity must be stated explicitly" },
  { obligation := .K1b_transportGradient,
    feeds := [.alignmentFactorization, .L1Budget, .measurabilityAndIntegrability],
    statusOpen := true,
    note := "transport control for regularized direction field without importing endpoint regularity" },
  { obligation := .K1c_nearFarBiotSavart,
    feeds := [.alignmentFactorization, .exceptionalTail],
    statusOpen := true,
    note := "principal-value-compatible near/far kernel decomposition with zero/singular cases handled" },
  { obligation := .K1d_uniformStrictGamma,
    feeds := [.viscosityMargin],
    statusOpen := true,
    note := "strict absorption constant must remain below one uniformly in epsilon, time and admissible approximation" },
  { obligation := .K1e_epsilonLimit,
    feeds := [.actualNSLimitPassage, .measurabilityAndIntegrability, .maximalTimePassage],
    statusOpen := true,
    note := "passes regularized inequalities to the actual solution and then to the maximal interval" },
  { obligation := .K1f_effectiveVolumeNormalization,
    feeds := [.noHiddenEndpointNorm, .alignmentFactorization, .cutoffNonCircularity],
    statusOpen := true,
    note := "prevents dimensional conversion or adaptive scale selection from importing an L-infinity/endpoint quantity" },
  { obligation := .tightness,
    feeds := [.actualNSLimitPassage, .viscosityMargin, .maximalTimePassage],
    statusOpen := true,
    note := "compactness alone does not preserve a strict gamma margin or a lifespan-uniform budget" }
]

/-- No single K1 item is designated as sufficient for G1-flex. -/
def K1ItemAloneClosesG1 (_ : K1Obligation) : Prop := False

/-- Metadata openness is not itself mathematical evidence. -/
def K1MetadataOpen (_ : K1GateDependency) : Prop := True

/-- Mechanical regression: the matrix contains seven explicit rows, including
the extra tightness obligation separated from K1a--K1f. -/
theorem k1BridgeMatrix_has_seven_rows :
    k1BridgeMatrix.length = 7 := by
  native_decide

/-- All currently encoded historical K1 obligations remain marked open. -/
theorem k1BridgeMatrix_all_open :
    ∀ x ∈ k1BridgeMatrix, x.statusOpen = true := by
  intro x hx
  simp [k1BridgeMatrix] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end MPrivate.NS.ThirdCoefficient
