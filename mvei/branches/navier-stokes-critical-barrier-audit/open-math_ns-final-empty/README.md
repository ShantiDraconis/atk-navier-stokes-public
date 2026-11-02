# navier-stokes-critical-barrier-audit — branch `open-math/ns-final-empty`

Lean sources from the branch `open-math/ns-final-empty` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `61132607c574ef079c1937a49726a922ff7fd512` (2026-09-27T10:55:41+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 74 — closed 2, conditional 0, open 0, proof error 0, not reached 0, no result 72.
* History: 226 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `8b2879624a38283495c40335dac1ffb17b812cd6ddbb35c895d1eb815ff11b7a`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/open-math_ns-final-empty/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `CriticalBarrier.OpenMath.NavierStokes.MinimalGreen.uniform_bulk_tail_implies_strict_signed_depletion` | `open-math/navier-stokes/actualns-g1/MinimalGreenCore.lean`:44 | nao_checado |
| `CriticalBarrier.OpenMath.NavierStokes.bulkTail_implies_openMathCore` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/G1StrictAdapter.lean`:48 | nao_checado |
| `CriticalBarrier.OpenMath.NavierStokes.g1Bridge_of_openMathCore` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/OpenMathCore.lean`:78 | nao_checado |
| `CriticalBarrier.OpenMath.NavierStokes.g1Producer_implies_openMathCore` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/G1StrictAdapter.lean`:37 | nao_checado |
| `CriticalBarrier.OpenMath.NavierStokes.global_regularity_from_actualNS_producer` | `open-math/navier-stokes/actualns-g1/ActualNSToG1Bridge.lean`:48 | nao_checado |
| `G1WeightedLow.gamma_effective_eq_neg35` | `formal/G1/WeightedLow.lean`:115 | nao_checado |
| `G1WeightedLow.gamma_effective_not_positive` | `formal/G1/WeightedLow.lean`:124 | nao_checado |
| `G1WeightedLow.no_canonical_absorption_at_gamma_effective` | `formal/G1/WeightedLow.lean`:128 | nao_checado |
| `NSActualNSToSubcriticalCoupling.actualNS_to_subcriticalCoupling` | `open-math/navier-stokes/claim/ActualNSToSubcriticalCouplingLane.lean`:115 | nao_checado |
| `NSActualNSToSubcriticalCoupling.subcriticalCoupling_of_controls` | `open-math/navier-stokes/claim/ActualNSToSubcriticalCouplingLane.lean`:102 | nao_checado |
| `NSAllCertifiedReuseMaster.enable_final_theorem_from_open_math_core` | `open-math/navier-stokes/claim/AllCertifiedReuseMaster.lean`:31 | nao_checado |
| `NSAllCertifiedReuseMaster.only_core_needed_for_terminal` | `open-math/navier-stokes/claim/AllCertifiedReuseMaster.lean`:58 | nao_checado |
| `NSAmplitudeInvariantNoGo.no_fixed_delta_from_amplitude_invariant_certificate` | `open-math/navier-stokes/logic-refutation/AmplitudeInvariantFixedDeltaNoGo.lean`:27 | nao_checado |
| `NSBulkTailTerminal.openMath_implies_strict_budget` | `open-math/navier-stokes/claim/BulkTailTerminal.lean`:102 | nao_checado |
| `NSBulkTailTerminal.producer_implies_uniform_margin` | `open-math/navier-stokes/claim/BulkTailTerminal.lean`:57 | nao_checado |
| `NSClaimProducers.ProofLane.actual_regularity_implies_habitability` | `open-math/navier-stokes/claim/ProofProducer.lean`:80 | nao_checado |
| `NSClaimProducers.ProofLane.inputs_imply_actual_regularity` | `open-math/navier-stokes/claim/ProofProducer.lean`:89 | nao_checado |
| `NSClaimProducers.ProofLane.inputs_imply_habitability` | `open-math/navier-stokes/claim/ProofProducer.lean`:71 | nao_checado |
| `NSClaimProducers.RefutationLane.all_actual_regular_excludes_refutation` | `open-math/navier-stokes/claim/RefutationProducer.lean`:77 | nao_checado |
| `NSClaimProducers.RefutationLane.exclusion_implies_actual_irregular` | `open-math/navier-stokes/claim/RefutationProducer.lean`:64 | nao_checado |
| `NSClaimProducers.RefutationLane.inputs_imply_exclusion` | `open-math/navier-stokes/claim/RefutationProducer.lean`:49 | nao_checado |
| `NSClaimTests.Proof.producer_implies_habitability` | `open-math/navier-stokes/claim/ProofLaneClaimTest.lean`:36 | nao_checado |
| `NSClaimTests.Refutation.producer_implies_exclusion` | `open-math/navier-stokes/claim/RefutationLaneClaimTest.lean`:39 | nao_checado |
| `NSClosedArchitecture.bulk_tail_closes_signed_depletion` | `open-math/navier-stokes/claim/NavierStokesClosedArchitecture.lean`:53 | nao_checado |
| `NSClosedArchitecture.g1_closes_if_downstream` | `open-math/navier-stokes/claim/NavierStokesClosedArchitecture.lean`:129 | nao_checado |
| `NSClosedArchitecture.navier_stokes_closed_from_G1` | `open-math/navier-stokes/claim/NavierStokesClosedArchitecture.lean`:140 | nao_checado |
| `NSClosedArchitecture.navier_stokes_closed_if_producers` | `open-math/navier-stokes/claim/NavierStokesClosedArchitecture.lean`:151 | nao_checado |
| `NSDualLane.Boundary.ready_requires_asymmetry` | `open-math/navier-stokes/claim/ScientificBoundary.lean`:22 | nao_checado |
| `NSDualLane.Proof.proof_lane_implies_habitability` | `open-math/navier-stokes/claim/ProofLane.lean`:53 | nao_checado |
| `NSDualLane.Refutation.refutation_lane_implies_refuted` | `open-math/navier-stokes/claim/RefutationLane.lean`:51 | nao_checado |
| `NSDualLaneTerminal.open_open_no_final_fail` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:117 | nao_checado |
| `NSDualLaneTerminal.open_open_no_root` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:121 | nao_checado |
| `NSDualLaneTerminal.open_open_not_ready` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:113 | nao_checado |
| `NSDualLaneTerminal.proof_and_refutation_closed_contradict` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:125 | nao_checado |
| `NSDualLaneTerminal.proof_terminal_ready` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:62 | nao_checado |
| `NSDualLaneTerminal.ready_implies_final_fail` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:80 | nao_checado |
| `NSDualLaneTerminal.ready_implies_root_present` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:89 | nao_checado |
| `NSDualLaneTerminal.refutation_terminal_ready` | `open-math/navier-stokes/claim/DualLaneTerminal.lean`:71 | nao_checado |
| `NSEnergyCompressionBarrier.fiber_unbounded_implies_no_energy_only_control` | `open-math/navier-stokes/logic-refutation/EnergyCompressionBarrier.lean`:26 | nao_checado |
| `NSEnergyCompressionBarrier.fiber_unbounded_implies_no_factorization` | `open-math/navier-stokes/logic-refutation/EnergyCompressionBarrier.lean`:49 | nao_checado |
| `NSFiberUnboundedFromScaling.scaling_witness_implies_fiber_unbounded` | `open-math/navier-stokes/logic-refutation/FiberUnboundedFromScaling.lean`:31 | nao_checado |
| `NSFinalAssembler.ready_implies_root_present` | `open-math/navier-stokes/claim/FinalRootAssembler.lean`:32 | nao_checado |
| `NSFinalAssembler.ready_requires_final_fail_sha` | `open-math/navier-stokes/claim/FinalRootAssembler.lean`:42 | nao_checado |
| `NSFinalProofClaim.final_proof_of_bridge` | `open-math/navier-stokes/claim/FINAL_PROOF_CLAIM.lean`:63 | nao_checado |
| `NSG1ProducerFastPath.bulkTail_implies_producer_exists` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/G1ProducerFastPath.lean`:90 | fechado |
| `NSG1ProducerFastPath.producer_implies_closed` | `formal/lean/CriticalBarrier/OpenMath/NavierStokes/G1ProducerFastPath.lean`:36 | fechado |
| `NSG1eActualNSMapCertificate.g1e_iff_open_math_core` | `open-math/navier-stokes/claim/G1eActualNSMapCertificate.lean`:42 | nao_checado |
| `NSG1eActualNSMapCertificate.g1e_implies_open_math_core` | `open-math/navier-stokes/claim/G1eActualNSMapCertificate.lean`:23 | nao_checado |
| `NSG1eActualNSMapCertificate.open_math_core_implies_g1e` | `open-math/navier-stokes/claim/G1eActualNSMapCertificate.lean`:32 | nao_checado |
| `NSHabitantCertificate.inhabitant_closes_terminal` | `open-math/navier-stokes/claim/NSHabitantCertificate.lean`:54 | nao_checado |
| `NSHabitantCertificate.ns_closed_of_blowup` | `open-math/navier-stokes/claim/NSHabitantCertificate.lean`:48 | nao_checado |
| `NSHabitantCertificate.ns_closed_of_global` | `open-math/navier-stokes/claim/NSHabitantCertificate.lean`:40 | nao_checado |
| `NSHabitantCertificate.open_math_producer_closes_terminal` | `open-math/navier-stokes/claim/NSHabitantCertificate.lean`:73 | nao_checado |
| `NSHabitantEnable.build_h_pos` | `open-math/navier-stokes/claim/NSHabitantEnable.lean`:45 | nao_checado |
| `NSHabitantEnable.enable_from_critical` | `open-math/navier-stokes/claim/NSHabitantEnable.lean`:77 | nao_checado |
| `NSHabitantEnable.enable_terminal_positive` | `open-math/navier-stokes/claim/NSHabitantEnable.lean`:69 | nao_checado |
| `NSLimitClosureF7F1.exact_material_gap` | `open-math/navier-stokes/claim/LimitClosureF7F1.lean`:84 | nao_checado |
| `NSLimitClosureF7F1.limit_property_closure` | `open-math/navier-stokes/claim/LimitClosureF7F1.lean`:52 | nao_checado |
| `NSLimitClosureF7F1.navier_stokes_limit_closure` | `open-math/navier-stokes/claim/LimitClosureF7F1.lean`:62 | nao_checado |
| `NSLimitClosureF7F1.open_math_producer_enables_theorem` | `open-math/navier-stokes/claim/LimitClosureF7F1.lean`:75 | nao_checado |
| `NSOpenMathCoreToG1Producer.openMathCore_implies_fastClosed` | `open-math/navier-stokes/claim/OpenMathCoreToG1Producer.lean`:42 | nao_checado |
| `NSOpenMathCoreToG1Producer.openMathCore_implies_fastProducerExists` | `open-math/navier-stokes/claim/OpenMathCoreToG1Producer.lean`:34 | nao_checado |
| `NSPositiveHabitantCore.open_math_exact` | `open-math/navier-stokes/claim/NSPositiveHabitantCore.lean`:42 | nao_checado |
| `NSPositiveHabitantCore.producer_enables_global` | `open-math/navier-stokes/claim/NSPositiveHabitantCore.lean`:27 | nao_checado |
| `NSQuantumClosureClaim.actualNS_closes_quantum_lane` | `open-math/navier-stokes/claim/QuantumClosureClaim.lean`:90 | nao_checado |
| `NSQuantumClosureClaim.close_of_realization` | `open-math/navier-stokes/claim/QuantumClosureClaim.lean`:72 | nao_checado |
| `NSThreeCaseClosure.close_open_math_of_admissible` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:52 | nao_checado |
| `NSThreeCaseClosure.enable_final_theorem` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:72 | nao_checado |
| `NSThreeCaseClosure.false_false_admissible` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:43 | nao_checado |
| `NSThreeCaseClosure.false_true_admissible` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:35 | nao_checado |
| `NSThreeCaseClosure.true_false_admissible` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:39 | nao_checado |
| `NSThreeCaseClosure.true_true_excluded` | `open-math/navier-stokes/claim/ThreeCaseClosure.lean`:31 | nao_checado |
| `NSUnconditionalClaimCertificate.certificate_enables_final_theorem` | `open-math/navier-stokes/claim/UnconditionalClaimCertificate.lean`:24 | nao_checado |
| `NSUnconditionalClaimCertificate.certificate_requires_open_math_core` | `open-math/navier-stokes/claim/UnconditionalClaimCertificate.lean`:38 | nao_checado |
