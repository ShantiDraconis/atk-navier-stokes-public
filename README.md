# ATK NAVIER-STOKES — Formal Research

Research repository maintained by Tiago Paschoalatto Fagliari (ORCID: https://orcid.org/0009-0006-6874-3910).

Status: **research in progress; no unconditional solution or Millennium Prize certification is claimed.**

This repository will preserve source paths, original commit SHAs, authorship, dependencies, and exact Lean verification outcomes. A successful Lean build does not by itself prove an original open problem unless the formalized theorem exactly matches it and all assumptions are discharged.

Related publication: https://doi.org/10.5281/zenodo.15164501 (historical publication; not a proof certificate).

Do not add confidential data or third-party code without checking its license and attribution.

<!-- mvei:start -->
## Lean sources and kernel check (MVEI)

[`imports/navier-stokes-critical-barrier-audit/`](imports/navier-stokes-critical-barrier-audit/) holds the Lean sources of `ShantiDraconis/navier-stokes-critical-barrier-audit` at commit `3904224` (2026-10-07): 385 files. In the MVEI verification the Lean kernel closed 1 174 theorems here (260 unique, without the lemmas Lean generates itself), with 2 conditional and 9 open (`sorry`). A closed theorem proves the statement written in the file; it is not a claim that an open problem is solved. Statements, axioms, the build log and how to reproduce: [`mvei/README.md`](mvei/README.md).
<!-- mvei:end -->

<!-- mvei-extra:start -->
## Other repositories published here

* [`imports/M-private/`](imports/M-private/) — Lean sources of `ShantiDraconis/M-private` at commit `ae69c0d` (2026-09-15): 94 files; the Lean kernel closed 813 theorems (269 unique, without auto-generated lemmas), 0 conditional, 0 open. Details: [`mvei/M-private/README.md`](mvei/M-private/README.md).
<!-- mvei-extra:end -->
