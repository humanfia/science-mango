# archon-physics

`archon-physics` is a local Lean 4 physics dependency synthesized with the
Archon faithful-grounding pipeline from Mathlib and Physlib. It formalizes the
finite, deterministic part of the thermal-physics roadmap and exposes that
interface to separate consumer targets.

## Release status

- One family: `source:wang2020_thermalization`
- 7 library modules, 15 capabilities, 96 locked public APIs
- Mathlib `v4.33.0`
- Physlib/PhysLean commit
  `846bc6814ee141aa945d7385646b6e45385e635e`
- `lake build`: passed
- Explicit `sorry`, `admit`, and `axiom` declarations: 0
- Release certificate:
  [release-certificate.json](.archon/physics-rebuild/release-certificate.json)
  (`5c2551b1dac46d2700de1e49ba2242cbf7479870294275a4ef548422b21041ac`)

## Formalized scope

The library includes:

- finite periodic lattice configurations and positive mass profiles;
- polynomial lattice Hamiltonians and their scaling identities;
- mass-weighted harmonic operators and finite normal-mode interfaces;
- entropy, approximate equipartition, hitting-time, and kinetic-time
  rescaling lemmas;
- the explicit finite microscopic Hamiltonian vector field;
- continuous differentiability of that vector field;
- existence and uniqueness of a nontrivial local solution germ through every
  finite initial state;
- pointwise and endpoint conservation of total momentum and Hamiltonian energy,
  conditional on the concrete ODE holding over the required interval.

The acceptance target
[problem_microscopic_dynamics.lean](ArchonPhysicsConsumers/Thermalization/problem_microscopic_dynamics.lean)
imports the generated `ArchonPhysics` dependency and combines the local
existence/uniqueness and conservation interfaces.

## Deliberate boundary

This release does **not** prove global existence of microscopic trajectories,
the random-disorder or thermodynamic limit, microscopic-to-kinetic convergence,
kinetic relaxation, equipartition from generic microscopic data, or a complete
thermalization law. Those steps require additional mathematical theorems; they
are not hidden behind assumptions or represented as proved APIs.

## Evidence

- Blueprint: [blueprint/src/content.tex](blueprint/src/content.tex)
- Microscopic chapter:
  [ArchonPhysics_MicroscopicDynamics.tex](blueprint/src/chapters/ArchonPhysics_MicroscopicDynamics.tex)
- Lean source:
  [MicroscopicDynamics.lean](ArchonPhysics/MicroscopicDynamics.lean)
- Faithful-grounding reports: [.archon/task_results](.archon/task_results)
- Locked campaign plan:
  [library-plan.locked.json](.archon/physics-rebuild/library-plan.locked.json)
- Lean symbol DAG:
  [lean-symbol-dag.json](.archon/physics-rebuild/lean-symbol-dag.json)

The blueprint doctor reports zero orphan chapters, broken or malformed
references, explicit axiom declarations, physics-modeling findings, and
grounding findings.

## Build

```bash
lake exe cache get
lake build
```

The Lake manifest pins both upstream dependency revisions. `.lake/` and other
generated build products are intentionally not part of the source release.

