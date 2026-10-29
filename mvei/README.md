# MVEI kernel check — navier-stokes-critical-barrier-audit

This folder records what the Lean 4 kernel said about the Lean sources of the private repository `ShantiDraconis/navier-stokes-critical-barrier-audit`. The sources are published in [`imports/navier-stokes-critical-barrier-audit/`](../imports/navier-stokes-critical-barrier-audit/).

## What is published

* Source: `ShantiDraconis/navier-stokes-critical-barrier-audit`, commit `3904224e49f7b2256d56ce19a5e11e7ddc93f524` (2026-10-07T22:45:16Z).
* 385 files: 312 `.lean` files and the Lake files (`lakefile.*`, `lean-toolchain`, `lake-manifest.json`), plus 20 license or origin file(s) that third-party code requires (`LICENSE`, `preservation/branch-snapshots/audit_correct-provenance-attribution-20260912/LICENSE`, `preservation/branch-snapshots/audit_final-two-stage-review-nsb2-20260912/LICENSE`…). Paths are the same as in the source repository.
* Nothing else from the private repository is published (documents, commercial license, prompts, storefront material).
* `SOURCES.sha256` lists every published file with its SHA-256. From the repository root: `sha256sum -c mvei/SOURCES.sha256`.

## What the kernel said

MVEI verification of 2026-10-29T01:06:09+00:00, on commit `3904224e49f7b2256d56ce19a5e11e7ddc93f524`. Each theorem was read with `Lean.collectAxioms`, the function behind `#print axioms`.

| Lean project | Lean version | Build | Closed | Conditional | Open (`sorry`) | Checked file by file: closed / conditional / open / proof error / not reached |
|---|---|---|---:|---:|---:|---|
| `.` | v4.19.0 | failed | 0 | 0 | 0 | 146 / 0 / 6 / 38 / 11 |
| `formal/lean` | v4.19.0 | failed | 0 | 0 | 0 | 99 / 1 / 0 / 6 / 6 |
| `formal/millennium/lean` | v4.19.0 | partial | 50 | 0 | 0 | 27 / 0 / 1 / 4 / 7 |
| `preservation/branch-snapshots/audit_correct-provenance-attribution-20260912/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/audit_final-two-stage-review-nsb2-20260912/formal/lean` | stable | partial | 149 | 0 | 0 | 10 / 0 / 0 / 1 / 27 |
| `preservation/branch-snapshots/audit_g1-beta-multiprover-20260913/formal/lean` | v4.19.0 | partial | 165 | 1 | 0 | 30 / 0 / 0 / 4 / 0 |
| `preservation/branch-snapshots/audit_g1-beta-multiprover-20260913/formal/millennium/lean` | v4.19.0 | partial | 128 | 0 | 0 | 3 / 0 / 0 / 3 / 0 |
| `preservation/branch-snapshots/audit_g1-prize-standard-v4-20260913/formal/millennium/lean` | v4.19.0 | OK | 71 | 0 | 0 | — |
| `preservation/branch-snapshots/audit_millennium-multiprover-structure-20260913/formal/lean` | stable | partial | 149 | 0 | 0 | 10 / 0 / 0 / 1 / 27 |
| `preservation/branch-snapshots/audit_millennium-multiprover-structure-20260913/formal/millennium/lean` | v4.19.0 | OK | 136 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_add-lre-ns-framework/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_audit-search-terms/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_claim-navier-stokes-git-evidence/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_compare-mathematical-formulas/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_execute-multi-agent-audit/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_fix-doc-date-error/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_navier-stokes-critical-barrier-audit/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_navier-stokes-noncircular-implementation/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_registro-git-navier-stokes/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_revendo-arquivos-auditoria/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_shanti-0-0-default-history/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_shanti-auditoria-ns/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_target-extractor/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_task-219265797-1361927617-c6bfd6e0-3c0d-429b-a267-9cea34423468/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/branch-snapshots/copilot_update-reference-section/formal/lean` | stable | OK | 0 | 0 | 0 | — |
| `preservation/session-scratch-20260913` | v4.19.0 | failed | 0 | 0 | 0 | 29 / 0 / 2 / 9 / 0 |

| Closed theorems in this repository | |
|---|---:|
| Counting each project | 1 202 |
| Unique (name + statement) | 561 |
| Unique, without the lemmas Lean generates itself (`eq_1`, `mk.inj`, `sizeOf_spec`, `deriving`) | 274 |

*Closed* means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`. It says that the statement as written in the file is proved; it does not say that an open problem is solved. Every statement is in `VERIFICACAO.json`. *Conditional* means the proof also uses axioms declared in the repository; *open* means it uses `sorry`. *Checked file by file* covers the files that no build reached: each one went through Lean whole, with a `#print axioms` for each theorem.

| Theorem | Project | State | Axioms beyond the standard three |
|---|---|---|---|
| `CriticalBarrierClayTarget.target_chain_is_explicit` | `preservation/branch-snapshots/audit_g1-beta-multiprover-20260913/formal/lean` | conditional | `CriticalBarrierClayTarget.LP_Bernstein_TARGET`, `CriticalBarrierClayTarget.CZ_Riesz_L32_TARGET`, `CriticalBarrierClayTarget.Sobolev_R3_TARGET`, `CriticalBarrierClayTarget.B2_12_ESS_TARGET`, `CriticalBarrierClayTarget.NS_GLOBAL_CLOSURE_TARGET` |
| `G1HypothesesV3.joint_law_and_tail_conditional_G1` | `. (file by file)` | open | `sorryAx` |
| `MillenniumAudit.StabilizedHypothetical.Perelman_like_22_25_3_1` | `. (file by file)` | open | `sorryAx` |
| `G1Dynamic.TrivialityAudit.fullChain_inhabited_for_every_ActualNS` | `. (file by file)` | open | `sorryAx` |
| `G1HypothesesV3.joint_law_and_tail_conditional_G1` | `. (file by file)` | open | `sorryAx` |
| `G1HypothesesV3.joint_law_and_tail_conditional_G1` | `. (file by file)` | open | `sorryAx` |
| `G1HypothesesV3.joint_law_and_tail_conditional_G1` | `. (file by file)` | open | `sorryAx` |
| `CriticalBarrierClayTarget.target_chain_is_explicit` | `formal/lean (file by file)` | conditional | `CriticalBarrierClayTarget.B2_12_ESS_TARGET`, `CriticalBarrierClayTarget.CZ_Riesz_L32_TARGET`, `CriticalBarrierClayTarget.LP_Bernstein_TARGET`, `CriticalBarrierClayTarget.NS_GLOBAL_CLOSURE_TARGET`, `CriticalBarrierClayTarget.Sobolev_R3_TARGET` |
| `G1HypothesesV3.joint_law_and_tail_conditional_G1` | `formal/millennium/lean (file by file)` | open | `sorryAx` |
| `G1HypothesesV3.joint_law_and_tail_conditional_G1` | `preservation/session-scratch-20260913 (file by file)` | open | `sorryAx` |
| `MillenniumAudit.StabilizedHypothetical.Perelman_like_22_25_3_1` | `preservation/session-scratch-20260913 (file by file)` | open | `sorryAx` |

### Declared theorems

The `.lean` files of the verified commit declare 670 `theorem`/`lemma` (counting copies). The kernel checked 524 of them (513 closed, 2 conditional, 9 open). The closed count in the table above is larger: it also counts the theorems Lean generates by itself (equation lemmas, structure fields, `deriving`), which are not written in the text. For 146 the kernel has no result:

| Reason | Theorems |
|---|---:|
| checked file by file: Lean did not reach the theorem (missing import, syntax error or timeout) | 78 |
| checked file by file: the written proof does not pass the kernel | 64 |
| the file did not compile (an error in it or in a file it imports) | 4 |

### MVEI corrections

* `correcoes/imports-no-topo.patch` (import fora do início do arquivo, 6 file(s)): applies to the published sources: `git apply -p1 --directory=imports/navier-stokes-critical-barrier-audit mvei/correcoes/imports-no-topo.patch` (in order, after the ones above)
* `correcoes/renomear-imports-mathlib.patch` (import de módulo que não existe na versão do Mathlib do projeto (renomeado ou dividido), 2 file(s)): applies to the published sources: `git apply -p1 --directory=imports/navier-stokes-critical-barrier-audit mvei/correcoes/renomear-imports-mathlib.patch` (in order, after the ones above)

## Files in this folder

* `VERIFICACAO.json` — each Lean project of this repository, each theorem the kernel read, its statement, its axioms and its state (`fechado` closed, `condicional` conditional, `aberto-sorry` open)
* `TEOREMAS.csv` — each declared `theorem`/`lemma`: file, line, state in the kernel (`nao_checado` = not checked) and, if not checked, why (in Portuguese)
* `BUILD_LOG.txt` — one block per project: Lean version, result, errors
* `SOURCE.json` — source commit, verified commit and dates, machine-readable
* `SOURCES.sha256` — SHA-256 of every published file

## Reproduce

```
cd imports/navier-stokes-critical-barrier-audit/<project>   # a project folder from the table above ('.' is imports/navier-stokes-critical-barrier-audit)
lake exe cache get           # only for projects that require Mathlib
lake build
```

Each project uses the Lean version in its own `lean-toolchain`, which elan installs. The MVEI pipeline that produced these results is in the author's repository and is not public.
