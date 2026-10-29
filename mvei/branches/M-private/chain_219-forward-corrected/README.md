# M-private — branch `chain/219-forward-corrected`

Lean sources from the branch `chain/219-forward-corrected` of the private repository `ShantiDraconis/M-private`, commit `574f30b6dd1df85d9c399291e29b3e1ce4c2342d` (2026-09-15T01:44:38+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 11 — closed 9, conditional 0, open 0, proof error 2, not reached 0, no result 0.
* History: 19 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `ed42212cbe01424ba979de92a43bac59d1336fee08ba0ccbb22a705edf17c806`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-private/chain_219-forward-corrected/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MPrivate.NS.ThirdCoefficient.concrete_signed_limit_preserves_cross_energy_gain` | `MPrivate/NS/ThirdCoefficient/SignedIntegralLimitConcrete.lean`:25 | fechado |
| `MPrivate.NS.ThirdCoefficient.defect_lower_bound_preserves_amplitude_multiple` | `MPrivate/NS/ThirdCoefficient/AlignmentBarrierGain.lean`:21 | fechado |
| `MPrivate.NS.ThirdCoefficient.energy_cannot_control_enstrophy_at_incompatible_scale` | `MPrivate/NS/ThirdCoefficient/SignedSpacetimeCrossNoGo.lean`:36 | fechado |
| `MPrivate.NS.ThirdCoefficient.integral_upper_bound_of_dominated_signed_truncations` | `MPrivate/NS/ThirdCoefficient/SignedIntegralLimitConcrete.lean`:8 | fechado |
| `MPrivate.NS.ThirdCoefficient.integrated_gain_of_uniform_signed_truncations` | `MPrivate/NS/ThirdCoefficient/SignedSpacetimeCrossGain.lean`:55 | erro |
| `MPrivate.NS.ThirdCoefficient.low_velocity_square_budget_from_heat_duhamel` | `MPrivate/NS/ThirdCoefficient/SignedSpacetimeCrossGain.lean`:84 | fechado |
| `MPrivate.NS.ThirdCoefficient.mixed_signed_block_nonzero_witness` | `MPrivate/NS/ThirdCoefficient/SignedSpacetimeCrossNoGo.lean`:6 | fechado |
| `MPrivate.NS.ThirdCoefficient.not_universal_mixed_block_cancellation` | `MPrivate/NS/ThirdCoefficient/SignedSpacetimeCrossNoGo.lean`:27 | fechado |
| `MPrivate.NS.ThirdCoefficient.signed_integrated_gain_closes_cross_budget` | `MPrivate/NS/ThirdCoefficient/SignedSpacetimeCrossGain.lean`:196 | erro |
| `MPrivate.NS.ThirdCoefficient.square_of_heat_duhamel_split` | `MPrivate/NS/ThirdCoefficient/SignedSpacetimeCrossGain.lean`:77 | fechado |
| `MPrivate.NS.ThirdCoefficient.uniform_cross_budget_from_integrated_gain` | `MPrivate/NS/ThirdCoefficient/ActualCrossBudget.lean`:70 | fechado |
