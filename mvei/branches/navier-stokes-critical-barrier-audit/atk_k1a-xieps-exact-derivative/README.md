# navier-stokes-critical-barrier-audit — branch `atk/k1a-xieps-exact-derivative`

Lean sources from the branch `atk/k1a-xieps-exact-derivative` of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `9566bf6467caf4f124e913e5c38f5bb89203eb4e` (2026-09-25T17:43:32+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 12 — closed 4, conditional 0, open 0, proof error 3, not reached 5, no result 0.
* History: 92 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `95cb99fa52cc40a2b1af5c5088897fc3bfc89a139e73165c5dd7bcf92650c799`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/navier-stokes-critical-barrier-audit/atk_k1a-xieps-exact-derivative/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `G1XiEpsExactAlgebra.eps_sq_le_r_eps_sq` | `formal/G1/XiEpsExactAlgebra.lean`:43 | erro |
| `G1XiEpsExactAlgebra.r_eps_ne_zero` | `formal/G1/XiEpsExactAlgebra.lean`:39 | fechado |
| `G1XiEpsExactAlgebra.r_eps_pos` | `formal/G1/XiEpsExactAlgebra.lean`:33 | fechado |
| `G1XiEpsExactAlgebra.r_eps_sq` | `formal/G1/XiEpsExactAlgebra.lean`:27 | erro |
| `G1XiEpsExactAlgebra.radialCoefficient_nonneg` | `formal/G1/XiEpsExactAlgebra.lean`:56 | erro |
| `G1XiEpsExactAlgebra.radialCoefficient_pos` | `formal/G1/XiEpsExactAlgebra.lean`:61 | fechado |
| `G1XiEpsExactAlgebra.xi_eps_eq_inv_smul` | `formal/G1/XiEpsExactAlgebra.lean`:48 | fechado |
| `MillenniumAudit.G1Uniformity.bridge_closes_uniform_G1` | `formal/millennium/lean/MillenniumAudit/G1Uniformity.lean`:33 | nao_alcancado |
| `MillenniumAudit.G1Uniformity.pointwise_does_not_imply_uniform_in_general` | `formal/millennium/lean/MillenniumAudit/G1Uniformity.lean`:69 | nao_alcancado |
| `MillenniumAudit.G1Uniformity.toy_not_uniform` | `formal/millennium/lean/MillenniumAudit/G1Uniformity.lean`:58 | nao_alcancado |
| `MillenniumAudit.G1Uniformity.toy_pointwise` | `formal/millennium/lean/MillenniumAudit/G1Uniformity.lean`:51 | nao_alcancado |
| `MillenniumAudit.G1Uniformity.uniform_implies_pointwise` | `formal/millennium/lean/MillenniumAudit/G1Uniformity.lean`:14 | nao_alcancado |
