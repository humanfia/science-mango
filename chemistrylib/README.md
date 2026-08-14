# ChemistryLib — verified mathematical chemistry

ChemistryLib is a source-grounded Lean library for reaction networks,
thermodynamics, kinetics, stochastic chemistry, photochemistry, and selected
chemical models. It is generated and checked through Archon's clean-room
library campaign without importing legacy Chemistry or CRNT implementations.

## Install and build

Install [elan](https://github.com/leanprover/elan), then clone the release
branch and enter this Lake project:

```bash
git clone --single-branch --branch ChemistryLib \
  https://github.com/menik1126/chemlib.git
cd chemlib/chemistrylib
lake build
lake env lean ChemistryLib.lean
```

The checked-in toolchain and manifest pin Lean, Mathlib, and Physlib. The first
build fetches those dependencies; subsequent builds reuse `.lake/`.

To consume ChemistryLib from another Lake project, use the repository's
`chemistrylib` subdirectory as the Git dependency and import `ChemistryLib`.
The repository-root README contains the exact `lakefile.toml` declaration.

## Release status

All thirteen ordinary capability families in the declared campaign DAG are
verified. The synthetic `chemistrylib.complete` root is also verified after its
independent sealed-holdout, standalone-extraction, clean-room, coverage, and
aggregate-build gates passed. It remains an aggregate root, not a fourteenth
ordinary family. The canonical global release-certificate hash is
`8f90fb79cb3c729eb77e99ad2842483860369032995fb92f1c3aaf8d691884fc`.

The current release adds the `autocatalysis.oscillation` family: integer
hyperflows, stoichiometric autocatalysis criteria, Milo/Nghe witnesses and
one-way dual-certificate soundness, an exact Oregonator Jacobian, separate
spectral-crossing and exact periodic-orbit certificates, and sealed-frontier
transfer under explicit dynamics-compatibility premises. A crossing certificate
alone is not presented as proof of a Hopf bifurcation or periodic motion.

## Grounding boundary

Mathlib is the general mathematical foundation. Physlib is reused through the
exact, hash-locked imports recorded in `campaign/grounding-policy.json`,
including units, quantum adapters, thermodynamic and statistical-mechanics
interfaces, and `Physlib.Mathematics.FDerivCurry`. The Physlib umbrella and
legacy Chemistry/CRNT implementations are forbidden dependencies.

## Verification

```bash
lake build
lake env lean ChemistryLib.lean
```

The public release can be compiled without Archon. Maintainers with the
separate generation controller can additionally replay the campaign-specific
validation workflow.

The reviewed CapabilityIR, module DAG, API lock, grounding policy, global-goal
binding, and release certificate are published under `campaign/`. The release
passes API ownership, axiom, symbol-DAG, migration, and full-build gates with no
`sorry`, `admit`, or project-defined axioms.
