# navier-stokes-critical-barrier-audit — branch `audit/closure-target-tree-v56`

Lean sources from the branch `audit/closure-target-tree-v56` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `31869e70b3262497afccef17eb571b40bfce6eed` (2026-09-13T19:19:17+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 3 — closed 1, conditional 0, open 0, proof error 2, not reached 0, no result 0.
* History: 7 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `372796c88633d2b94c9e57e7173b67eb011ed8a888dfef0ba88d265f8645d9cc`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/audit_closure-target-tree-v56/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `G1Audit.hDynamic_from_dynamic_campanato` | `formal/G1/DynamicCampanato.lean`:134 | fechado |
| `G1Audit.hDynamic_if_campanato_closes` | `formal/G1/G1_DynamicCriticalGeometry.lean`:67 | erro |
| `G1Audit.signed_depletion_if_dynamic_geometry_closes` | `formal/G1/G1_DynamicCriticalGeometry.lean`:91 | erro |
