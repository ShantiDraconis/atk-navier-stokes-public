# navier-stokes-critical-barrier-audit — branch `open-math/ns-final-empty`

Lean sources from the branch `open-math/ns-final-empty` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `61132607c574ef079c1937a49726a922ff7fd512` (2026-09-27T10:55:41+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 74 — closed 58, conditional 0, open 0, proof error 3, not reached 13, no result 0.
* History: 226 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `7d22bf82c4f1eda3892c57da864c7a3275f2b74e189c42fec1873cf07439cdf9`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/open-math_ns-final-empty/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `CriticalBarrier.OpenMath.NavierStokes.MinimalGreen.uniform_bulk_tail_implies_strict_signed_depletion` | `open-math/navier-stokes/actualns-g1/MinimalGreenCore.lean`:44 | fechado |
| `CriticalBarrier.OpenMath.NavierStokes.bulkTail_implies_openMathCore` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/G1StrictAdapter.lean`:48 | nao_alcancado |
| `CriticalBarrier.OpenMath.NavierStokes.g1Bridge_of_openMathCore` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/OpenMathCore.lean`:78 | nao_alcancado |
| `CriticalBarrier.OpenMath.NavierStokes.g1Producer_implies_openMathCore` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/G1StrictAdapter.lean`:37 | nao_alcancado |
| `CriticalBarrier.OpenMath.NavierStokes.global_regularity_from_actualNS_producer` | `open-math/navier-stokes/actualns-g1/ActualNSToG1Bridge.lean`:48 | nao_alcancado |
| `G1WeightedLow.gamma_effective_eq_neg35` | `formal/G1/WeightedLow.lean`:115 | fechado |
| `G1WeightedLow.gamma_effective_not_positive` | `formal/G1/WeightedLow.lean`:124 | fechado |
| `G1WeightedLow.no_canonical_absorption_at_gamma_effective` | `formal/G1/WeightedLow.lean`:128 | fechado |
| `NSActualNSToSubcriticalCoupling.actualNS_to_subcriticalCoupling` | `open-math/navier-stokes/claim/ActualNSToSubcriticalCouplingLane.lean`:115 | fechado |
| `NSActualNSToSubcriticalCoupling.subcriticalCoupling_of_controls` | `open-math/navier-stokes/claim/ActualNSToSubcriticalCouplingLane.lean`:102 | fechado |
| `NSAllCertifiedReuseMaster.enable_final_theorem_from_open_math_core` | `open-math/navier-stokes/claim/AllCertifiedReuseMaster.lean`:31 | nao_alcancado |
| `NSAllCertifiedReuseMaster.only_core_needed_for_terminal` | `open-math/navier-stokes/claim/AllCertifiedReuseMaster.lean`:58 | nao_alcancado |
| `NSAmplitudeInvariantNoGo.no_fixed_delta_from_amplitude_invariant_certificate` | `open-math/navier-stokes/logic-refutation/AmplitudeInvariantFixedDeltaNoGo.lean`:27 | fechado |
| `NSBulkTailTerminal.openMath_implies_strict_budget` | `open-math/navier-stokes/claim/BulkTailTerminal.lean`:102 | fechado |
| `NSBulkTailTerminal.producer_implies_uniform_margin` | `open-math/navier-stokes/claim/BulkTailTerminal.lean`:57 | fechado |
| `NSClaimProducers.ProofLane.actual_regularity_implies_habitability` | `open-math/navier-stokes/claim/ProofProducer.lean`:80 | fechado |
| `NSClaimProducers.ProofLane.inputs_imply_actual_regularity` | `open-math/navier-stokes/claim/ProofProducer.lean`:89 | fechado |
| `NSClaimProducers.ProofLane.inputs_imply_habitability` | `open-math/navier-stokes/claim/ProofProducer.lean`:71 | fechado |
| `NSClaimProducers.RefutationLane.all_actual_regular_excludes_refutation` | `open-math/navier-stokes/claim/RefutationProducer.lean`:77 | fechado |
| `NSClaimProducers.RefutationLane.exclusion_implies_actual_irregular` | `open-math/navier-stokes/claim/RefutationProducer.lean`:64 | fechado |
| `NSClaimProducers.RefutationLane.inputs_imply_exclusion` | `open-math/navier-stokes/claim/RefutationProducer.lean`:49 | fechado |
| `NSClaimTests.Proof.producer_implies_habitability` | `open-math/navier-stokes/claim/ProofLaneClaimTest.lean`:36 | fechado |
| `NSClaimTests.Refutation.producer_implies_exclusion` | `open-math/navier-stokes/claim/RefutationLaneClaimTest.lean`:39 | fechado |
| `NSClosedArchitecture.bulk_tail_closes_signed_depletion` | `open-math/navier-stokes/claim/NavierStokesClosedArchitecture.lean`:53 | fechado |
| `NSClosedArchitecture.g1_closes_if_downstream` | `open-math/navier-stokes/claim/NavierStokesClosedArchitecture.lean`:129 | fechado |
| `NSClosedArchitecture.navier_stokes_closed_from_G1` | `open-math/navier-stokes/claim/NavierStokesClosedArchitecture.lean`:140 | fechado |
| `NSClosedArchitecture.navier_stokes_closed_if_producers` | `open-math/navier-stokes/claim/NavierStokesClosedArchitecture.lean`:151 | fechado |
| `NSDualLane.Boundary.ready_requires_asymmetry` | `open-math/navier-stokes/claim/ScientificBoundary.lean`:22 | fechado |
| `NSDualLane.Proof.proof_lane_implies_habitability` | `open-math/navier-stokes/claim/ProofLane.lean`:53 | fechado |
| `NSDualLane.Refutation.refutation_lane_implies_refuted` | `open-math/navier-stokes/claim/RefutationLane.lean`:51 | fechado |
| `NSDualLaneTerminal.open_open_no_final_fail` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:117 | fechado |
| `NSDualLaneTerminal.open_open_no_root` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:121 | fechado |
| `NSDualLaneTerminal.open_open_not_ready` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:113 | fechado |
| `NSDualLaneTerminal.proof_and_refutation_closed_contradict` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:125 | fechado |
| `NSDualLaneTerminal.proof_terminal_ready` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:62 | fechado |
| `NSDualLaneTerminal.ready_implies_final_fail` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:80 | fechado |
| `NSDualLaneTerminal.ready_implies_root_present` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:89 | fechado |
| `NSDualLaneTerminal.refutation_terminal_ready` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:71 | fechado |
| `NSEnergyCompressionBarrier.fiber_unbounded_implies_no_energy_only_control` | `open-math/navier-stokes/logic-refutation/EnergyCompressionBarrier.lean`:26 | fechado |
| `NSEnergyCompressionBarrier.fiber_unbounded_implies_no_factorization` | `open-math/navier-stokes/logic-refutation/EnergyCompressionBarrier.lean`:49 | fechado |
| `NSFiberUnboundedFromScaling.scaling_witness_implies_fiber_unbounded` | `open-math/navier-stokes/logic-refutation/FiberUnboundedFromScaling.lean`:31 | fechado |
| `NSFinalAssembler.ready_implies_root_present` | `open-math/navier-stokes/claim/FinalRootAssembler.lean`:32 | fechado |
| `NSFinalAssembler.ready_requires_final_fail_sha` | `open-math/navier-stokes/claim/FinalRootAssembler.lean`:42 | fechado |
| `NSFinalProofClaim.final_proof_of_bridge` | `open-math/navier-stokes/claim/FINAL_PROOF_CLAIM.lean`:63 | fechado |
| `NSG1ProducerFastPath.bulkTail_implies_producer_exists` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/G1ProducerFastPath.lean`:90 | fechado |
| `NSG1ProducerFastPath.producer_implies_closed` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/G1ProducerFastPath.lean`:36 | fechado |
| `NSG1eActualNSMapCertificate.g1e_iff_open_math_core` | `open-math/navier-stokes/claim/G1eActualNSMapCertificate.lean`:42 | nao_alcancado |
| `NSG1eActualNSMapCertificate.g1e_implies_open_math_core` | `open-math/navier-stokes/claim/G1eActualNSMapCertificate.lean`:23 | nao_alcancado |
| `NSG1eActualNSMapCertificate.open_math_core_implies_g1e` | `open-math/navier-stokes/claim/G1eActualNSMapCertificate.lean`:32 | nao_alcancado |
| `NSHabitantCertificate.inhabitant_closes_terminal` | `open-math/navier-stokes/claim/NSHabitantCertificate.lean`:54 | fechado |
| `NSHabitantCertificate.ns_closed_of_blowup` | `open-math/navier-stokes/claim/NSHabitantCertificate.lean`:48 | fechado |
| `NSHabitantCertificate.ns_closed_of_global` | `open-math/navier-stokes/claim/NSHabitantCertificate.lean`:40 | fechado |
| `NSHabitantCertificate.open_math_producer_closes_terminal` | `open-math/navier-stokes/claim/NSHabitantCertificate.lean`:73 | fechado |
| `NSHabitantEnable.build_h_pos` | `open-math/navier-stokes/claim/NSHabitantEnable.lean`:45 | erro |
| `NSHabitantEnable.enable_from_critical` | `open-math/navier-stokes/claim/NSHabitantEnable.lean`:77 | erro |
| `NSHabitantEnable.enable_terminal_positive` | `open-math/navier-stokes/claim/NSHabitantEnable.lean`:69 | erro |
| `NSLimitClosureF7F1.exact_material_gap` | `open-math/navier-stokes/claim/LimitClosureF7F1.lean`:84 | fechado |
| `NSLimitClosureF7F1.limit_property_closure` | `open-math/navier-stokes/claim/LimitClosureF7F1.lean`:52 | fechado |
| `NSLimitClosureF7F1.navier_stokes_limit_closure` | `open-math/navier-stokes/claim/LimitClosureF7F1.lean`:62 | fechado |
| `NSLimitClosureF7F1.open_math_producer_enables_theorem` | `open-math/navier-stokes/claim/LimitClosureF7F1.lean`:75 | fechado |
| `NSOpenMathCoreToG1Producer.openMathCore_implies_fastClosed` | `open-math/navier-stokes/claim/OpenMathCoreToG1Producer.lean`:42 | nao_alcancado |
| `NSOpenMathCoreToG1Producer.openMathCore_implies_fastProducerExists` | `open-math/navier-stokes/claim/OpenMathCoreToG1Producer.lean`:34 | nao_alcancado |
| `NSPositiveHabitantCore.open_math_exact` | `open-math/navier-stokes/claim/NSPositiveHabitantCore.lean`:42 | fechado |
| `NSPositiveHabitantCore.producer_enables_global` | `open-math/navier-stokes/claim/NSPositiveHabitantCore.lean`:27 | fechado |
| `NSQuantumClosureClaim.actualNS_closes_quantum_lane` | `open-math/navier-stokes/claim/QuantumClosureClaim.lean`:90 | fechado |
| `NSQuantumClosureClaim.close_of_realization` | `open-math/navier-stokes/claim/QuantumClosureClaim.lean`:72 | fechado |
| `NSThreeCaseClosure.close_open_math_of_admissible` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:52 | fechado |
| `NSThreeCaseClosure.enable_final_theorem` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:72 | fechado |
| `NSThreeCaseClosure.false_false_admissible` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:43 | fechado |
| `NSThreeCaseClosure.false_true_admissible` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:35 | fechado |
| `NSThreeCaseClosure.true_false_admissible` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:39 | fechado |
| `NSThreeCaseClosure.true_true_excluded` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:31 | fechado |
| `NSUnconditionalClaimCertificate.certificate_enables_final_theorem` | `open-math/navier-stokes/claim/UnconditionalClaimCertificate.lean`:24 | nao_alcancado |
| `NSUnconditionalClaimCertificate.certificate_requires_open_math_core` | `open-math/navier-stokes/claim/UnconditionalClaimCertificate.lean`:38 | nao_alcancado |
