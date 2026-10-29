# navier-stokes-critical-barrier-audit — branch `copilot/primitive-to-bridge`

Lean sources from the branch `copilot/primitive-to-bridge` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `f3e4e85de7558b1ee807238f9f3696fbaf9edbaf` (2026-09-13T17:31:53+00:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 4 — closed 2, conditional 0, open 0, proof error 2, not reached 0, no result 0.
* History: 1 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `74dee3e2f135932c5a981e0ae03b1bdc07b59eec673090eb45c23903e6064cbb`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/copilot_primitive-to-bridge/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `G1Audit.dynamic_campanato_of_bridge` | `formal/G1/DynamicCampanato.lean`:233 | fechado |
| `G1Audit.gamma_diff_lt_half` | `formal/G1/DynamicCampanato.lean`:443 | erro |
| `G1Audit.gamma_half_closes_campanato` | `formal/G1/DynamicCampanato.lean`:469 | erro |
| `G1Audit.remainder_integral_from_energy` | `formal/G1/DynamicCampanato.lean`:71 | fechado |
