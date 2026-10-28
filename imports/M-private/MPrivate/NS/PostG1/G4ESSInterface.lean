import Mathlib

namespace MPrivate.NS.PostG1

/-!
# G4ESSInterface

This file does not re-prove Escauriaza--Seregin--Sverak. It records the exact
mapping obligations needed before an externally supplied endpoint theorem may
be invoked in the Navier--Stokes chain.

The mapping structure stores propositions; `ESSMappingHolds` is the proof-level
conjunction that must actually be discharged.  A status tag or a populated
record alone is not an endpoint certificate.

Audit directionality rule: G4 is strictly downstream.  An endpoint invocation
must consume the actual G3 critical bound for the same solution and maximal
interval; it may never be recycled to establish G1, T3, T4, the cross budget,
or the G3 bound itself.
-/

variable {Solution : Type*}

/-- Abstract endpoint theorem input package. -/
structure EndpointInput (Solution : Type*) where
  solution : Solution
  maximalTime : ℝ
  criticalBound : ℝ

/-- Repository-side hypothesis mapping to the external endpoint theorem. -/
structure ESSHypothesisMap (Solution : Type*) where
  solutionClassMatches : Prop
  domainMatches : Prop
  timeIntervalMatches : Prop
  incompressibilityMatches : Prop
  pressureRegularityMatches : Prop
  criticalSpaceIsL3 : Prop
  criticalBoundUniformOnMaximalInterval : Prop
  maximalLifespanConventionMatches : Prop
  endpointBoundIsActualNormNotProxy : Prop
  same_solution_as_G3_output : Prop
  same_maximal_interval_as_G3_output : Prop
  same_critical_norm_as_G3_output : Prop
  same_bound_constant_as_G3_output_or_stronger : Prop
  G3_bound_derived_before_endpoint_invocation : Prop
  downstream_of_G1_only : Prop
  not_used_to_establish_G1 : Prop
  not_used_to_establish_T3 : Prop
  not_used_to_establish_T4 : Prop
  not_used_to_establish_cross_budget : Prop
  not_used_to_establish_G3 : Prop
  finiteTimeConventionMatches : Prop
  externalTheoremStatementPinned : Prop
  externalReferencePinned : Prop

/-- Proof-level discharge of every mapping proposition. -/
def ESSMappingHolds (m : ESSHypothesisMap Solution) : Prop :=
  m.solutionClassMatches ∧
  m.domainMatches ∧
  m.timeIntervalMatches ∧
  m.incompressibilityMatches ∧
  m.pressureRegularityMatches ∧
  m.criticalSpaceIsL3 ∧
  m.criticalBoundUniformOnMaximalInterval ∧
  m.maximalLifespanConventionMatches ∧
  m.endpointBoundIsActualNormNotProxy ∧
  m.same_solution_as_G3_output ∧
  m.same_maximal_interval_as_G3_output ∧
  m.same_critical_norm_as_G3_output ∧
  m.same_bound_constant_as_G3_output_or_stronger ∧
  m.G3_bound_derived_before_endpoint_invocation ∧
  m.downstream_of_G1_only ∧
  m.not_used_to_establish_G1 ∧
  m.not_used_to_establish_T3 ∧
  m.not_used_to_establish_T4 ∧
  m.not_used_to_establish_cross_budget ∧
  m.not_used_to_establish_G3 ∧
  m.finiteTimeConventionMatches ∧
  m.externalTheoremStatementPinned ∧
  m.externalReferencePinned

/-- Continuation conclusion expected from the external endpoint theorem. -/
def EndpointContinuationConclusion
    (finiteMaximalTimeExcluded : Prop) : Prop :=
  finiteMaximalTimeExcluded

/-- Audit object: an endpoint invocation is admissible only with a proof of the
full mapping and a proof of the continuation conclusion supplied by the pinned
external theorem.  This repository does not manufacture either proof. -/
structure AdmissibleEndpointInvocation (Solution : Type*) where
  input : EndpointInput Solution
  mapping : ESSHypothesisMap Solution
  mappingCertified : ESSMappingHolds mapping
  finiteMaximalTimeExcluded : Prop
  continuationCertified : EndpointContinuationConclusion finiteMaximalTimeExcluded

inductive G4Status where
  | externalMappingPending
  | mappedConditional
  | externallyCertified
  deriving DecidableEq, Repr

end MPrivate.NS.PostG1
