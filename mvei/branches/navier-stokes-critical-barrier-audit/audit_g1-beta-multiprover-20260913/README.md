# navier-stokes-critical-barrier-audit — branch `audit/g1-beta-multiprover-20260913`

Lean sources from the branch `audit/g1-beta-multiprover-20260913` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `74f5413f14016c548d8c1d8ea407bef5adad0236` (2026-09-13T18:56:43+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 12 — closed 7, conditional 0, open 0, proof error 5, not reached 0, no result 0.
* History: 13 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `2154f79ae38e9961d5152dbe22bacba30f79173e2961ceb5051394e3cb45b899`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/audit_g1-beta-multiprover-20260913/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `CriticalBarrier.AlignmentTransport.qJoint_nonneg` | `formal/lean/CriticalBarrier/AlignmentTransport.lean`:27 | erro |
| `CriticalBarrier.AlignmentTransport.transport_after_absorption` | `formal/lean/CriticalBarrier/AlignmentTransport.lean`:51 | erro |
| `CriticalBarrier.EntropyObstruction.beltrami_naive_entropy_negative` | `formal/lean/CriticalBarrier/EntropyObstruction.lean`:13 | fechado |
| `CriticalBarrier.EntropyObstruction.beltrami_naive_entropy_positive` | `formal/lean/CriticalBarrier/EntropyObstruction.lean`:32 | fechado |
| `CriticalBarrier.EntropyObstruction.beltrami_naive_entropy_threshold` | `formal/lean/CriticalBarrier/EntropyObstruction.lean`:24 | fechado |
| `CriticalBarrier.MillenniumCore.adapter_scalar_core` | `formal/lean/CriticalBarrier/MillenniumCore.lean`:155 | fechado |
| `CriticalBarrier.MillenniumCore.corrected_remainder_eq_sq` | `formal/lean/CriticalBarrier/MillenniumCore.lean`:26 | fechado |
| `CriticalBarrier.MillenniumCore.corrected_remainder_nonneg` | `formal/lean/CriticalBarrier/MillenniumCore.lean`:32 | fechado |
| `CriticalBarrier.WeightedLow.audit_constant_36` | `formal/lean/CriticalBarrier/WeightedLow.lean`:83 | fechado |
| `CriticalBarrier.WeightedLow.etaLow_tendsto_zero` | `formal/lean/CriticalBarrier/WeightedLow.lean`:24 | erro |
| `CriticalBarrier.WeightedLow.residual_dissipation_positive` | `formal/lean/CriticalBarrier/WeightedLow.lean`:103 | erro |
| `CriticalBarrier.WeightedLow.strict_absorption` | `formal/lean/CriticalBarrier/WeightedLow.lean`:69 | erro |
