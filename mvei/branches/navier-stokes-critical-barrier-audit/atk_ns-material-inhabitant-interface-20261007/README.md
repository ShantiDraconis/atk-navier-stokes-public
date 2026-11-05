# navier-stokes-critical-barrier-audit — branch `atk/ns-material-inhabitant-interface-20261007`

Lean sources from the branch `atk/ns-material-inhabitant-interface-20261007` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `c6877d55772ebffd6e18ac31f7c6f51141176864` (2026-10-07T16:04:53+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 10 — closed 9, conditional 0, open 0, proof error 1, not reached 0, no result 0.
* History: 19 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `adf77b6657eb965928abd47e4d9f08092021cd3e095a0cf8a9c9bdd94392c11a`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/atk_ns-material-inhabitant-interface-20261007/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `NSProducerFirst.ClayClosureCertificate.provesClayA` | `audit/producer-first/ClayGlobalRegularityClosure.lean`:121 | fechado |
| `NSProducerFirst.clay_A_from_material` | `audit/producer-first/ClayGlobalRegularityClosure.lean`:95 | fechado |
| `NSProducerFirst.clay_dependency_chain` | `audit/producer-first/ClayGlobalRegularityClosure.lean`:42 | fechado |
| `NSProducerFirst.clay_global_regularity_from_material` | `audit/producer-first/ClayGlobalRegularityClosure.lean`:64 | fechado |
| `NSProducerFirst.material_to_uniform_enstrophy` | `audit/producer-first/MaterialPromotionFull.lean`:77 | fechado |
| `NSProducerFirst.promotedByMaterial_global` | `audit/producer-first/MaterialPromotionFull.lean`:162 | fechado |
| `NSProducerFirst.promotedByMaterial_proves_ClayA` | `audit/producer-first/MaterialPromotionFull.lean`:202 | erro |
| `NSProducerFirst.promotedByMaterial_requires_material` | `audit/producer-first/MaterialPromotionFull.lean`:216 | fechado |
| `NSProducerFirst.recovered_bulk_tail_closes_material` | `audit/producer-first/RecoveredMaterialRoute.lean`:196 | fechado |
| `NSProducerFirst.recovered_route_is_sufficient` | `audit/producer-first/RecoveredMaterialRoute.lean`:118 | fechado |
