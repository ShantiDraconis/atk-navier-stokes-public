# navier-stokes-critical-barrier-audit — branch `attack/ns003-o1-core-v419`

Lean sources from the branch `attack/ns003-o1-core-v419` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `a8e724a912d200fef4ee046f3952dca39e64bde3` (2026-09-26T10:03:17+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 17 — closed 8, conditional 0, open 0, proof error 3, not reached 6, no result 0.
* History: 114 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `923de2e25e74fc55700d6bdf7439e6f177acc1a543deeb1ca83872b62da96aa1`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/attack_ns003-o1-core-v419/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `CriticalBarrier.EnergyLaws.finite` | `formal/lean/CriticalBarrier/Energy.lean`:12 | erro |
| `CriticalBarrier.EnergyLaws.scaling` | `formal/lean/CriticalBarrier/Energy.lean`:14 | erro |
| `CriticalBarrier.PressureLaws.compatibility` | `formal/lean/CriticalBarrier/Pressure.lean`:11 | erro |
| `MillenniumAudit.NS003.CKNAdapter.epsilon_regular_region_control` | `formal/G1/NS003CKNAdapter.lean`:11 | nao_alcancado |
| `MillenniumAudit.NS003.CKNAdapter.gradient_epsilon_regular_region_control` | `formal/G1/NS003CKNAdapter.lean`:45 | nao_alcancado |
| `MillenniumAudit.NS003.O1ActualNSUniformQJoint_implies_concrete_O1` | `formal/G1/NS003O1Concrete.lean`:98 | fechado |
| `MillenniumAudit.NS003.O1_O2_O3_close_flexible_G1` | `formal/G1/NS003FirstGap.lean`:45 | nao_alcancado |
| `MillenniumAudit.NS003.O1_O2_O3_to_uniform_enstrophy` | `formal/G1/NS003FirstGap.lean`:64 | nao_alcancado |
| `MillenniumAudit.NS003.O1_currently_uninhabited` | `formal/G1/NS003FirstGap.lean`:92 | nao_alcancado |
| `MillenniumAudit.NS003.O1_from_atomic_components` | `formal/millennium/lean/MillenniumAudit/NS003O1Atomic.lean`:83 | nao_alcancado |
| `MillenniumAudit.NS003.O1_from_components` | `formal/G1/NS003O1Concrete.lean`:69 | fechado |
| `MillenniumAudit.NS003.QJointTrajectory.nonneg` | `formal/G1/NS003O1Concrete.lean`:21 | fechado |
| `MillenniumAudit.NS003.StrictSignedDepletionProducer` | `formal/G1/StrictSignedDepletionProducer.lean`:9 | fechado |
| `MillenniumAudit.NS003.StrictSignedDepletionProducer_delta` | `formal/G1/StrictSignedDepletionProducer.lean`:29 | fechado |
| `MillenniumAudit.NS003.signed_depletion_balance_implies_G1` | `formal/G1/NS003EndpointTheorem.lean`:54 | fechado |
| `MillenniumAudit.NS003.strict_signed_depletion_to_genuine_G1` | `formal/G1/NS003EndpointTheorem.lean`:8 | fechado |
| `MillenniumAudit.NS003.strict_signed_route_uses_budget_not_fixed_delta` | `formal/G1/StrictSignedDepletionProducer.lean`:50 | fechado |
