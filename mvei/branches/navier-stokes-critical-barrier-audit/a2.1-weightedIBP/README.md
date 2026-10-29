# navier-stokes-critical-barrier-audit — branch `a2.1-weightedIBP`

Lean sources from the branch `a2.1-weightedIBP` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `79140147ba92fe290b4178f92ff7d77ec3271198` (2026-09-14T02:59:28+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 100 — closed 100, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 137 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `d410f48f67d3df540f24af5487181ac214a538687b8bbc6aea85714ceebd321e`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/a2.1-weightedIBP/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `G1Audit.LocalEnergyIdentityData.ofXiEpsPDE_identity` | `formal/G1/XiEpsLocalizedRealization.lean`:393 | fechado |
| `G1Audit.LocalizedCutoff.grad_rho_power` | `formal/G1/XiEpsLocalizedRealization.lean`:68 | fechado |
| `G1Audit.LocalizedCutoff.lap_rho_power` | `formal/G1/XiEpsLocalizedRealization.lean`:72 | fechado |
| `G1Audit.SpaceTimeProductTransfer.goodSlices_ae` | `formal/G1/WeakOmegaSliceInterface.lean`:86 | fechado |
| `G1Audit.StrainKernelData.apply_symmetric` | `formal/G1/StrainKernel.lean`:44 | fechado |
| `G1Audit.StrainKernelData.apply_trace_zero` | `formal/G1/StrainKernel.lean`:53 | fechado |
| `G1Audit.WeakOmegaSpaceTime.dt_memSobolev_zero` | `formal/G1/WeakOmegaBridge.lean`:49 | fechado |
| `G1Audit.WeakOmegaSpaceTime.dx_memSobolev_zero` | `formal/G1/WeakOmegaBridge.lean`:54 | fechado |
| `G1Audit.WeakOmegaSpaceTime.lineDeriv_memSobolev_zero` | `formal/G1/WeakOmegaBridge.lean`:43 | fechado |
| `G1Audit.WeakOmegaSpaceTime.memSobolev_zero` | `formal/G1/WeakOmegaBridge.lean`:37 | fechado |
| `G1Audit.WeakOmegaSpaceTime.omegaL2_spec` | `formal/G1/WeakOmegaBridge.lean`:65 | fechado |
| `G1Audit.WeakOmegaSpaceTime.omegaProd_memLp` | `formal/G1/SpaceTimeCoordinateSplit.lean`:154 | fechado |
| `G1Audit.WeakOmegaSpaceTime.omegaProd_slice_memLp_ae` | `formal/G1/SpaceTimeCoordinateSplit.lean`:164 | fechado |
| `G1Audit.WeakOmegaSpaceTime.productSlicesGood_ae` | `formal/G1/SpaceTimeCoordinateSplit.lean`:176 | fechado |
| `G1Audit.WeakOmegaSpaceTime.spatialDerivativeCommonFullSet_compl_null` | `formal/G1/SeparatedSpatialWeakDerivativeIdentity.lean`:48 | fechado |
| `G1Audit.WeakOmegaSpaceTime.spatialDerivative_testSeq_ae_common` | `formal/G1/SeparatedSpatialWeakDerivativeIdentity.lean`:18 | fechado |
| `G1Audit.WeakOmegaSpaceTime.spatialDerivative_test_ae` | `formal/G1/WeakOmegaSpatialSlice.lean`:42 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDirectionalL2_spec` | `formal/G1/WeakOmegaBridge.lean`:76 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDtL2_spec` | `formal/G1/WeakOmegaBridge.lean`:87 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDxL2_spec` | `formal/G1/WeakOmegaBridge.lean`:98 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDxProd_memLp` | `formal/G1/SpaceTimeCoordinateSplit.lean`:159 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDxProd_slice_memLp_ae` | `formal/G1/SpaceTimeCoordinateSplit.lean`:170 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDx_productSchwartz_pairing` | `formal/G1/WeakOmegaProductPairing.lean`:48 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDx_productSpatial_integral_pairing` | `formal/G1/WeakOmegaProductPairing.lean`:69 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDx_productSpatial_pairing` | `formal/G1/WeakOmegaProductPairing.lean`:59 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDx_schwartz_pairing` | `formal/G1/WeakOmega4DPairing.lean`:23 | fechado |
| `G1Audit.WeakOmegaSpaceTime.weakDx_schwartz_pairing_dist` | `formal/G1/WeakOmega4DPairing.lean`:38 | fechado |
| `G1Audit.WeakXiSpaceTime.dt_memSobolev_zero` | `formal/G1/WeakDerivBridge.lean`:58 | fechado |
| `G1Audit.WeakXiSpaceTime.dx_memSobolev_zero` | `formal/G1/WeakDerivBridge.lean`:63 | fechado |
| `G1Audit.WeakXiSpaceTime.exists_lineDeriv_L2_rep` | `formal/G1/VectorLocalRep.lean`:17 | fechado |
| `G1Audit.WeakXiSpaceTime.lineDeriv_memSobolev_zero` | `formal/G1/WeakDerivBridge.lean`:52 | fechado |
| `G1Audit.WeakXiSpaceTime.memSobolev_one_two` | `formal/G1/WeakDerivBridge.lean`:49 | fechado |
| `G1Audit.WeakXiSpaceTime.weakDirectionalL2_spec` | `formal/G1/VectorLocalRep.lean`:36 | fechado |
| `G1Audit.WeakXiSpaceTime.weakDtL2_spec` | `formal/G1/VectorLocalRep.lean`:27 | fechado |
| `G1Audit.WeakXiSpaceTime.weakDxL2_spec` | `formal/G1/VectorLocalRep.lean`:46 | fechado |
| `G1Audit.XiEpsLocalizedRealization.diffusionIBP` | `formal/G1/XiEpsLocalizedRealization.lean`:266 | fechado |
| `G1Audit.XiEpsLocalizedRealization.localized_identity` | `formal/G1/XiEpsLocalizedRealization.lean`:307 | fechado |
| `G1Audit.XiEpsLocalizedRealization.strainSplitPair` | `formal/G1/XiEpsLocalizedRealization.lean`:259 | fechado |
| `G1Audit.XiEpsLocalizedRealization.testedEquation` | `formal/G1/XiEpsLocalizedRealization.lean`:282 | fechado |
| `G1Audit.XiEpsPDE.DtXi_eq_rhs` | `formal/G1/XiEpsLocalizedRealization.lean`:93 | fechado |
| `G1Audit.XiEpsPDE.R1_denominator_ne_zero` | `formal/G1/XiEpsPDE.lean`:115 | fechado |
| `G1Audit.XiEpsPDE.R2_denominator_ne_zero` | `formal/G1/XiEpsPDE.lean`:120 | fechado |
| `G1Audit.XiEpsPDE.bochnerPair_equation` | `formal/G1/XiEpsLocalizedRealization.lean`:99 | fechado |
| `G1Audit.ae_eq_zero_of_time_smooth_tests` | `formal/G1/WeakOmegaSliceInterface.lean`:61 | fechado |
| `G1Audit.ballMeanBound` | `formal/G1/BallMeanBound.lean`:43 | fechado |
| `G1Audit.campanato_linear_half_step` | `formal/G1/DynamicCampanatoArithmetic.lean`:27 | fechado |
| `G1Audit.finFourEquivTimeSpace_spatial` | `formal/G1/SpaceTimeSpatialDirection.lean`:16 | fechado |
| `G1Audit.firstMomentIntegrand_even` | `formal/G1/StrainKernelMoments.lean`:36 | fechado |
| `G1Audit.gamma_lt_half_of_kappa` | `formal/G1/DynamicCampanatoArithmetic.lean`:13 | fechado |
| `G1Audit.gamma_lt_half_of_linearClosure` | `formal/G1/DynamicCampanato.lean`:71 | fechado |
| `G1Audit.geometric_half_sum_le_two` | `formal/G1/DynamicCampanato.lean`:94 | fechado |
| `G1Audit.gronwall_factor_36` | `formal/G1/DynamicCampanato.lean`:138 | fechado |
| `G1Audit.integral_comp_productToSpaceTime` | `formal/G1/SpaceTimeIntegralTransport.lean`:32 | fechado |
| `G1Audit.integral_comp_spaceTimeToProduct` | `formal/G1/SpaceTimeIntegralTransport.lean`:41 | fechado |
| `G1Audit.integral_sq_norm_eq_iterated` | `formal/G1/WeakOmegaSliceInterface.lean`:50 | fechado |
| `G1Audit.l2RepToProduct_memLp` | `formal/G1/SpaceTimeCoordinateSplit.lean`:140 | fechado |
| `G1Audit.l2RepToProduct_memLp_volume` | `formal/G1/SpaceTimeCoordinateSplit.lean`:129 | fechado |
| `G1Audit.lineDeriv_productSchwartzPullback` | `formal/G1/WeakOmegaProductPairing.lean`:32 | fechado |
| `G1Audit.linearClosure_of_C` | `formal/G1/DynamicCampanato.lean`:81 | fechado |
| `G1Audit.linear_rate_one_step` | `formal/G1/DynamicCampanato.lean`:158 | fechado |
| `G1Audit.magEps_ne_zero` | `formal/G1/XiEpsPDE.lean`:41 | fechado |
| `G1Audit.magEps_nonneg` | `formal/G1/XiEpsPDE.lean`:29 | fechado |
| `G1Audit.magEps_pos` | `formal/G1/XiEpsPDE.lean`:34 | fechado |
| `G1Audit.magEps_sq` | `formal/G1/WeakDiffusionIBP.lean`:25 | fechado |
| `G1Audit.memLp_two_spatialSlice_ae` | `formal/G1/WeakOmegaSliceInterface.lean`:27 | fechado |
| `G1Audit.neg_lineDeriv_productSchwartzPullback` | `formal/G1/WeakOmegaProductPairing.lean`:40 | fechado |
| `G1Audit.norm_le_magEps` | `formal/G1/WeakDiffusionIBP.lean`:32 | fechado |
| `G1Audit.productSchwartzPullback_apply` | `formal/G1/WeakOmegaProductPairing.lean`:26 | fechado |
| `G1Audit.productSpaceTimeMeasure_eq_volume` | `formal/G1/SpaceTimeCoordinateSplit.lean`:121 | fechado |
| `G1Audit.productTensorSchwartz_apply` | `formal/G1/TensorProductSchwartz.lean`:73 | fechado |
| `G1Audit.productTensorSchwartz_spatial_lineDeriv_apply` | `formal/G1/TensorProductSpatialDerivative.lean`:22 | fechado |
| `G1Audit.productToSpaceTime_measurePreserving` | `formal/G1/SpaceTimeCoordinateSplit.lean`:75 | fechado |
| `G1Audit.productToSpaceTime_spaceTimeToProduct` | `formal/G1/SpaceTimeCoordinateSplit.lean`:98 | fechado |
| `G1Audit.recurrence_rhs_factor` | `formal/G1/DynamicCampanato.lean`:46 | fechado |
| `G1Audit.recurrence_step_bound` | `formal/G1/DynamicCampanato.lean`:53 | fechado |
| `G1Audit.spaceTimeProductCLE_apply` | `formal/G1/SpaceTimeCoordinateSplit.lean`:111 | fechado |
| `G1Audit.spaceTimeProductCLE_spatialDirection` | `formal/G1/SpaceTimeSpatialDirection.lean`:34 | fechado |
| `G1Audit.spaceTimeProductCLE_symm_apply` | `formal/G1/SpaceTimeCoordinateSplit.lean`:116 | fechado |
| `G1Audit.spaceTimeProductHomeomorph_apply` | `formal/G1/TensorProductSchwartz.lean`:89 | fechado |
| `G1Audit.spaceTimeProductHomeomorph_symm_apply` | `formal/G1/TensorProductSchwartz.lean`:94 | fechado |
| `G1Audit.spaceTimeProductMeasurableEquiv_apply` | `formal/G1/SpaceTimeIntegralTransport.lean`:22 | fechado |
| `G1Audit.spaceTimeProductMeasurableEquiv_symm_apply` | `formal/G1/SpaceTimeIntegralTransport.lean`:27 | fechado |
| `G1Audit.spaceTimeReindex_spatialDirection` | `formal/G1/SpaceTimeSpatialDirection.lean`:21 | fechado |
| `G1Audit.spaceTimeSplitL2_measurePreserving` | `formal/G1/SpaceTimeCoordinateSplit.lean`:48 | fechado |
| `G1Audit.spaceTimeTensorRaw_contDiff` | `formal/G1/TensorProductSchwartz.lean`:112 | fechado |
| `G1Audit.spaceTimeTensorRaw_hasCompactSupport` | `formal/G1/TensorProductSchwartz.lean`:103 | fechado |
| `G1Audit.spaceTimeTensorSchwartz_apply` | `formal/G1/TensorProductSchwartz.lean`:132 | fechado |
| `G1Audit.spaceTimeToProduct_measurePreserving` | `formal/G1/SpaceTimeCoordinateSplit.lean`:55 | fechado |
| `G1Audit.spaceTimeToProduct_productToSpaceTime` | `formal/G1/SpaceTimeCoordinateSplit.lean`:92 | fechado |
| `G1Audit.spatialWeakResidual_ae_zero` | `formal/G1/WeakOmegaSpatialSlice.lean`:30 | fechado |
| `G1Audit.strainComponent_odd` | `formal/G1/StrainKernelMoments.lean`:22 | fechado |
| `G1Audit.subtract_constant_identity` | `formal/G1/StrainKernelMoments.lean`:46 | fechado |
| `G1Audit.support_tensorProductRaw_subset` | `formal/G1/TensorProductSchwartz.lean`:35 | fechado |
| `G1Audit.tensorProductRaw_contDiff` | `formal/G1/TensorProductSchwartz.lean`:25 | fechado |
| `G1Audit.tensorProductRaw_hasCompactSupport` | `formal/G1/TensorProductSchwartz.lean`:49 | fechado |
| `G1Audit.weightedIBP_component` | `formal/G1/WeakDiffusionIBP.lean`:142 | fechado |
| `G1Audit.weightedIBP_vector_component` | `formal/G1/WeakDiffusionIBP.lean`:156 | fechado |
| `G1Audit.xiEps_norm_le_one` | `formal/G1/WeakDiffusionIBP.lean`:40 | fechado |
| `G1Audit.xiEps_norm_le_one_for_mean` | `formal/G1/BallMeanBound.lean`:17 | fechado |
| `G1Audit.xiEps_sub_mean_norm_le_two` | `formal/G1/WeakDiffusionIBP.lean`:55 | fechado |
