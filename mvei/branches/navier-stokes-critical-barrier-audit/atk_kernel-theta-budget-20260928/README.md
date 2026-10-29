# navier-stokes-critical-barrier-audit — branch `atk/kernel-theta-budget-20260928`

Lean sources from the branch `atk/kernel-theta-budget-20260928` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `4416414f1b3ad007dbbb625689b8151a0a10432b` (2026-09-28T13:56:42+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 85 — closed 56, conditional 0, open 0, proof error 2, not reached 27, no result 0.
* History: 150 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `aa13c2d0cb5f7c57787eaf49e079d4c5bcf15d499a94693dc80c964d4783d116`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/atk_kernel-theta-budget-20260928/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `CriticalBarrier.ExternalFastPath.compose_external` | `formal/lean/CriticalBarrier/ExternalFastPath.lean`:48 | fechado |
| `CriticalBarrier.ExternalFastPath.promoted_three_gate_plus_balance` | `formal/lean/CriticalBarrier/ExternalFastPath.lean`:67 | fechado |
| `CriticalBarrier.ExternalRouteRouter.next_ne_self` | `formal/lean/CriticalBarrier/ExternalRouteRouter.lean`:33 | fechado |
| `CriticalBarrier.ExternalRouteRouter.next_strictly_advances` | `formal/lean/CriticalBarrier/ExternalRouteRouter.lean`:28 | fechado |
| `CriticalBarrier.K1aClaimGate.conflicting_evidence_blocks_claim` | `formal/lean/CriticalBarrier/K1aClaimGate.lean`:25 | fechado |
| `CriticalBarrier.K1aClaimGate.unknown_proof_blocks_claim` | `formal/lean/CriticalBarrier/K1aClaimGate.lean`:17 | fechado |
| `CriticalBarrier.K1aClaimGate.unknown_refutation_blocks_claim` | `formal/lean/CriticalBarrier/K1aClaimGate.lean`:21 | fechado |
| `CriticalBarrier.K1aExactFrechetProducer.chainRuleStatement_closed_of_differentiableAt` | `formal/lean/CriticalBarrier/K1aExactFrechetProducer.lean`:96 | fechado |
| `CriticalBarrier.K1aExactFrechetProducer.exactDerivativeStatement_closed` | `formal/lean/CriticalBarrier/K1aExactFrechetProducer.lean`:77 | fechado |
| `CriticalBarrier.K1aExactFrechetProducer.inverseRadiusDerivativeMap` | `formal/lean/CriticalBarrier/K1aExactFrechetProducer.lean`:12 | fechado |
| `CriticalBarrier.K1aExactFrechetProducer.productDerivativeMap` | `formal/lean/CriticalBarrier/K1aExactFrechetProducer.lean`:29 | fechado |
| `CriticalBarrier.K1aExactFrechetProducer.xiFrechetTarget_closed` | `formal/lean/CriticalBarrier/K1aExactFrechetProducer.lean`:72 | fechado |
| `CriticalBarrier.K1aExactFrechetProducer.xi_chainRule_of_hasDerivAt` | `formal/lean/CriticalBarrier/K1aExactFrechetProducer.lean`:82 | fechado |
| `CriticalBarrier.K1aExactFrechetProducer.xi_hasFDerivAt_DxiCLM` | `formal/lean/CriticalBarrier/K1aExactFrechetProducer.lean`:40 | fechado |
| `CriticalBarrier.K1aFrechet.exactDerivative_from_target` | `formal/lean/CriticalBarrier/K1aFrechet.lean`:25 | fechado |
| `CriticalBarrier.K1aPDELift.DxiLinearityTarget_closed` | `formal/lean/CriticalBarrier/K1aPDELift.lean`:41 | fechado |
| `CriticalBarrier.K1aPDELift.XiMaterialTarget_closed` | `formal/lean/CriticalBarrier/K1aPDELift.lean`:48 | fechado |
| `CriticalBarrier.K1aVectorKernel.DxiCLM_apply` | `formal/lean/CriticalBarrier/K1aVectorKernel.lean`:88 | fechado |
| `CriticalBarrier.K1aVectorKernel.DxiCandidate_add` | `formal/lean/CriticalBarrier/K1aVectorKernel.lean`:60 | fechado |
| `CriticalBarrier.K1aVectorKernel.DxiCandidate_radial_form` | `formal/lean/CriticalBarrier/K1aVectorKernel.lean`:38 | fechado |
| `CriticalBarrier.K1aVectorKernel.DxiCandidate_smul` | `formal/lean/CriticalBarrier/K1aVectorKernel.lean`:68 | fechado |
| `CriticalBarrier.K1aVectorKernel.r_ne_zero` | `formal/lean/CriticalBarrier/K1aVectorKernel.lean`:28 | fechado |
| `CriticalBarrier.K1aVectorKernel.r_pos` | `formal/lean/CriticalBarrier/K1aVectorKernel.lean`:23 | fechado |
| `CriticalBarrier.K1aVectorKernel.r_sq` | `formal/lean/CriticalBarrier/K1aVectorKernel.lean`:32 | fechado |
| `CriticalBarrier.K1aXiEps.eps_le_sqrt_rSq` | `formal/G1/XiEpsChainRule.lean`:26 | erro |
| `CriticalBarrier.K1aXiEps.eps_sq_div_rsq_le_one` | `formal/G1/XiEpsChainRule.lean`:57 | fechado |
| `CriticalBarrier.K1aXiEps.rSq_pos` | `formal/G1/XiEpsChainRule.lean`:15 | fechado |
| `CriticalBarrier.K1aXiEps.radial_defect_scalar` | `formal/G1/XiEpsChainRule.lean`:35 | erro |
| `CriticalBarrier.K1aXiEps.radial_eigenvalue_scalar` | `formal/G1/XiEpsChainRule.lean`:43 | fechado |
| `CriticalBarrier.K1aXiEps.sqrt_rSq_pos` | `formal/G1/XiEpsChainRule.lean`:21 | fechado |
| `CriticalBarrier.KernelPromotedG1Assembly.balance_and_G1flex_give_differential_inequality` | `formal/lean/CriticalBarrier/KernelPromotedG1Assembly.lean`:22 | fechado |
| `CriticalBarrier.KernelPromotedG1Assembly.pointwiseTheta_nonnegative` | `formal/lean/CriticalBarrier/KernelPromotedG1Assembly.lean`:73 | fechado |
| `CriticalBarrier.KernelPromotedG1Assembly.pointwiseTheta_strictly_less_than_one` | `formal/lean/CriticalBarrier/KernelPromotedG1Assembly.lean`:82 | fechado |
| `CriticalBarrier.KernelPromotedG1Assembly.three_gate_gives_G1flex` | `formal/lean/CriticalBarrier/KernelPromotedG1Assembly.lean`:91 | fechado |
| `CriticalBarrier.KernelPromotedG1Assembly.three_gate_plus_balance_gives_differential` | `formal/lean/CriticalBarrier/KernelPromotedG1Assembly.lean`:104 | fechado |
| `CriticalBarrier.KernelPromotedG1Assembly.three_gate_pointwise_assembles` | `formal/lean/CriticalBarrier/KernelPromotedG1Assembly.lean`:61 | fechado |
| `CriticalBarrier.ScientificMeet.conflict_cannot_issue` | `formal/G1/ScientificMeet.lean`:52 | fechado |
| `CriticalBarrier.ScientificMeet.meet_disproved_disproved` | `formal/G1/ScientificMeet.lean`:34 | fechado |
| `CriticalBarrier.ScientificMeet.meet_disproved_proved` | `formal/G1/ScientificMeet.lean`:31 | fechado |
| `CriticalBarrier.ScientificMeet.meet_proved_disproved` | `formal/G1/ScientificMeet.lean`:28 | fechado |
| `CriticalBarrier.ScientificMeet.meet_proved_proved` | `formal/G1/ScientificMeet.lean`:25 | fechado |
| `CriticalBarrier.ScientificMeet.meet_unknown_left` | `formal/G1/ScientificMeet.lean`:37 | fechado |
| `CriticalBarrier.ScientificMeet.meet_unknown_right` | `formal/G1/ScientificMeet.lean`:41 | fechado |
| `CriticalBarrier.ScientificMeet.neither_cannot_issue` | `formal/G1/ScientificMeet.lean`:60 | fechado |
| `CriticalBarrier.ScientificMeet.openMath_cannot_issue` | `formal/G1/ScientificMeet.lean`:56 | fechado |
| `G1DynamicCampanato.proved_identity_interface_accepts_vacuous_pde` | `formal/G1/DynamicCampanato.lean`:165 | fechado |
| `G1FailProofAllGaps.ALL_EXPOSED_GAPS_FAIL_PROOF` | `formal/G1/FailProofAllGaps.lean`:340 | nao_alcancado |
| `G1FailProofAllGaps.G2_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:157 | nao_alcancado |
| `G1FailProofAllGaps.G3_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:174 | nao_alcancado |
| `G1FailProofAllGaps.G4_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:187 | nao_alcancado |
| `G1FailProofAllGaps.GENERIC_NS_BRIDGE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:311 | nao_alcancado |
| `G1FailProofAllGaps.K1A_INVENTORY_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:34 | nao_alcancado |
| `G1FailProofAllGaps.K1B_INVENTORY_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:36 | nao_alcancado |
| `G1FailProofAllGaps.K1B_TRANSPORT_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:53 | nao_alcancado |
| `G1FailProofAllGaps.K1C_INVENTORY_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:37 | nao_alcancado |
| `G1FailProofAllGaps.K1C_K1D_ABSORPTION_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:68 | nao_alcancado |
| `G1FailProofAllGaps.K1D_INVENTORY_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:38 | nao_alcancado |
| `G1FailProofAllGaps.K1D_WEIGHTED_ABSORPTION_DERIVATION_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:83 | nao_alcancado |
| `G1FailProofAllGaps.K1E_INTEGRABILITY_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:104 | nao_alcancado |
| `G1FailProofAllGaps.K1E_INVENTORY_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:39 | nao_alcancado |
| `G1FailProofAllGaps.K1E_LIMIT_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:117 | nao_alcancado |
| `G1FailProofAllGaps.K1F_DIMENSIONAL_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:134 | nao_alcancado |
| `G1FailProofAllGaps.K1F_INVENTORY_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:40 | nao_alcancado |
| `G1FailProofAllGaps.NS_B1_UNDERSPECIFIED_CLASS` | `formal/G1/FailProofAllGaps.lean`:199 | nao_alcancado |
| `G1FailProofAllGaps.NS_B2_CRITICAL_BRIDGE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:204 | nao_alcancado |
| `G1FailProofAllGaps.NS_B3_ESS_MAP_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:211 | nao_alcancado |
| `G1FailProofAllGaps.NS_B4_ZERO_BRANCH_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:226 | nao_alcancado |
| `G1FailProofAllGaps.NS_B5_COERCIVITY_FIELD_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:239 | nao_alcancado |
| `G1FailProofAllGaps.NS_B6_CORRECTION_FIELDS_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:252 | nao_alcancado |
| `G1FailProofAllGaps.NS_B7_PRESSURE_FIELD_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:263 | nao_alcancado |
| `G1FailProofAllGaps.NS_B8_FORCING_FIELD_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:273 | nao_alcancado |
| `G1FailProofAllGaps.NS_B9_MEAN_TO_CRITICAL_FIELD_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:286 | nao_alcancado |
| `G1FailProofAllGaps.STATE_CLOSURE_INTERFACE_VACUOUS` | `formal/G1/FailProofAllGaps.lean`:335 | nao_alcancado |
| `G1FailProofFinal.CURRENT_ARCHITECTURE_FAIL_PROOF` | `formal/G1/FailProofFinal.lean`:69 | fechado |
| `G1FailProofFinal.absorption_route_countercertificate` | `formal/G1/FailProofFinal.lean`:30 | fechado |
| `G1FailProofFinal.coherence_interface_countercertificate` | `formal/G1/FailProofFinal.lean`:37 | fechado |
| `G1FailProofFinal.dynamic_campanato_countercertificate` | `formal/G1/FailProofFinal.lean`:51 | fechado |
| `G1FailProofFinal.fullchain_interface_countercertificate` | `formal/G1/FailProofFinal.lean`:41 | fechado |
| `G1FailProofFinal.xieps_interface_countercertificate` | `formal/G1/FailProofFinal.lean`:45 | fechado |
| `G1WeightedLow.gamma_effective_cannot_bound_positive_gamma` | `formal/G1/WeightedLow.lean`:120 | fechado |
| `G1WeightedLow.gamma_effective_not_pos` | `formal/G1/WeightedLow.lean`:53 | fechado |
| `G1XiEpsPDE.XiEpsPDE.equation_holds` | `formal/G1/XiEpsPDE.lean`:233 | fechado |
| `G1XiEpsPDE.regularizedChainMap_unfold` | `formal/G1/XiEpsPDE.lean`:87 | fechado |
| `G1XiEpsPDE.xieps_record_allows_vacuous_equation` | `formal/G1/XiEpsPDE.lean`:309 | fechado |
| `G1XiEpsPDE.xieps_record_allows_vacuous_local_energy_test` | `formal/G1/XiEpsPDE.lean`:313 | fechado |
