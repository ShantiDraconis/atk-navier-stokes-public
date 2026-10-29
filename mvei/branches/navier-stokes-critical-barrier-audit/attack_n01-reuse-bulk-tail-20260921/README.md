# navier-stokes-critical-barrier-audit — branch `attack/n01-reuse-bulk-tail-20260921`

Lean sources from the branch `attack/n01-reuse-bulk-tail-20260921` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `c38eb14bbb8ded956c0d0780b0c3112afcba1dd5` (2026-09-21T12:54:00+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 10 — closed 10, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 101 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `f7181a88278d85e9de3d29a829fb8836d5bbf1055c6725ef4d1d01f0fa23bbde`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/attack_n01-reuse-bulk-tail-20260921/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `G1Dynamic.bulk_tail_reuse_closes_dynamic_G1` | `formal/G1/N01WeightedClosureReuse.lean`:27 | fechado |
| `G1Dynamic.geometricDepletion_iff_v3` | `formal/G1/N01WeightedClosureReuse.lean`:20 | fechado |
| `G1Dynamic.hardened_bridge_preserves_constant_control` | `formal/G1/G1_DynamicCriticalGeometry_Hardened.lean`:107 | fechado |
| `G1Dynamic.inner_normalizedTangentialPart_eq_zero` | `formal/G1/G1_DynamicCriticalGeometry_Hardened.lean`:27 | fechado |
| `G1Dynamic.kernelBudgetCertificate_closes` | `formal/G1/N01WeightedClosureReuse.lean`:54 | fechado |
| `G1Dynamic.normalizedTangentialPart_eq_tangentialPart_of_unit` | `formal/G1/G1_DynamicCriticalGeometry_Hardened.lean`:42 | fechado |
| `G1Dynamic.quantitative_coherence_exports_bound` | `formal/G1/G1_DynamicCriticalGeometry_Hardened.lean`:69 | fechado |
| `G1Dynamic.toV3_stretch` | `formal/G1/N01WeightedClosureReuse.lean`:17 | fechado |
| `G1Dynamic.toV3_z` | `formal/G1/N01WeightedClosureReuse.lean`:14 | fechado |
| `G1Dynamic.xiEpsTangentialPart_orthogonal` | `formal/G1/G1_DynamicCriticalGeometry_Hardened.lean`:124 | fechado |
