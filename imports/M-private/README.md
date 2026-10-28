# M-private

Private adversarial certification workspace for the M-program.

## Governance

- This repository is the only writable development workspace for the current cycle.
- Historical repositories, including `navier-stokes-critical-barrier-audit`, are read-only sources of provenance and previously certified material.
- No `MFinal/NS/GlobalRegularity.lean` is created before the ThirdCoefficient candidate passes every required gate.
- New development uses no `sorry`, `admit`, or new mathematical `axiom` declarations.
- A compiling theorem is not automatically a Clay-level result. Status and dependencies must be recorded explicitly.

## Current target

For 3D Navier–Stokes, isolate a non-circular coefficient `a₃[u]` with critical temporal scaling

`a₃[u_λ](t) = λ² a₃[u](λ² t)`

such that the vortex-stretching contribution can be controlled schematically by

`V ≤ ε Z + C a₃ Y`

and `∫ a₃` is controlled without importing the sought regularity conclusion or an equivalent continuation criterion.

The current strategy has moved beyond searching for a better critical norm. The active target is signed/aligned vortex-stretching cancellation before absolute values destroy geometric information.

## Current module

`MPrivate/NS/ThirdCoefficient/`

contains the specification, scaling and circularity classifiers, the `‖S‖₃²` candidate and its energy-budget no-go theorem, and the signed/aligned/spectral next-stage obligations.

No final regularity theorem is claimed here.
