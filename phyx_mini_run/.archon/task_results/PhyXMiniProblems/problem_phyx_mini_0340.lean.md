# Autoformalization result: `problem_phyx_mini_0340.lean` (iteration 002)

## Retry-gate resolution

The review gate requested a real Lake/Mathlib check because the earlier target
did not directly import Mathlib. The file now has `import Mathlib` in addition
to the two focused Physlib unit imports. The complete physical statement was
re-audited against the source report, blueprint, and primary image rather than
being reduced to an import-only smoke test, and it was compiled with the
project's `lake env lean` environment.

## Assumption/target split

### Governing laws

- `SatisfiesFirstLaw model` states `ΔU = Q - W_by` for every
  `ThermodynamicPath`, using coherent SI joule readouts.
- `ThermodynamicModel.internalEnergy` depends only on a
  `ThermodynamicState`, while `heatIntoSystem` and `workDoneBySystem` depend on
  the whole path. This is the endpoint/path distinction needed to compare the
  two routes from `a` to `b`.
- The sign convention is explicit: heat into the system and work done by the
  system are positive.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesSuppliedFigure figure` records the pressure and volume axes, origin
  label `O`, the p-V placement of `a`, `b`, `c`, and `d`, and all relevant
  directed arrows.
- Primary-image inspection gives `a → c → b` as isochoric then
  isobaric, `a → d → b` as isobaric then isochoric, and the blue curved
  arrow as `b → a`. This corrects the inconsistent auxiliary caption.
- `hHeatACB` records `Q_acb = 90 J`.
- `hWorkACB` records `W_by,acb = 60 J`.
- `hWorkADB` records `W_by,adb = 15 J`.
- `AnswerChoice.jouleValue` records only the four printed option values:
  A = 15, B = 45, C = 25, D = 32 joules. It does not assert which option is
  physically correct.

### Current target conclusion

- `energyInJoules (model.heatIntoSystem figure.pathADB) = 45`, i.e. the heat
  entering along `adb` is `45 J` (choice B).

## Goal-faithfulness audit

The `45 J` conclusion occurs only as the conclusion of
`heatIntoSystemAlongADB_eq_45_joules` (and as the literal printed beside
answer-choice label B). It is not a hypothesis, a field of
`ThermodynamicModel`, part of `SatisfiesFirstLaw`, or part of
`MatchesSuppliedFigure`. Unfolding any local definition does not prove the
main theorem: one must use the supplied `90 J`, `60 J`, and `15 J` data with
the first law and the fact that both paths have endpoints `a` and `b`.

The model preserves physical roles: pressure, volume, heat, work, and
internal energy are dimensionful quantities. Reals are used only for named SI
readouts and answer-option values. No physical primitive was reduced to a
transparent scalar alias or one-field scalar wrapper.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0340:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0340.heatIntoSystemAlongADB_eq_45_joules`.
- Dimensioned quantities/readouts: `VolumeQuantity`, `PressureQuantity`,
  `EnergyQuantity`, `volumeInCubicMetres`, `pressureInPascals`, and
  `energyInJoules`.
- Physical state/path vocabulary: `ThermodynamicState`, `ProcessKind`,
  `ProcessLeg`, `ThermodynamicPath`, `IsTwoLegPathVia`, and `IsOneLegPath`.
- Figure vocabulary: `AxisQuantity`, `PVFigure`, `HasDisplayedPVGeometry`, and
  `MatchesSuppliedFigure`.
- Governing model/law: `ThermodynamicModel` and `SatisfiesFirstLaw`.
- Displayed options: `AnswerChoice` and `AnswerChoice.jouleValue`.

The blueprint chapter was not edited because the task's explicit write
permissions forbid blueprint edits. The orchestrator/plan agent should add
`\lean{PhyXMiniProblems.ProblemPhyXMini0340.heatIntoSystemAlongADB_eq_45_joules}`
and `\leanok` to its target environment.

## LeanExplore queries and candidates

All searches used `packages: ["Mathlib", "Physlib"]`.

- `first law of thermodynamics internal energy heat work thermodynamic path`
  returned `MicroHamiltonian.internalU`, Mathlib's topological `Path`,
  statistical-mechanics declarations, and `DimEnergy`. The first three are
  near misses: none models general path-dependent heat/work with the first law.
- `dimensionful SI energy pressure volume physical units` returned and
  grounded `UnitChoices.SI`, `DimPressure`, `Dimensionful`, and `DimEnergy`.
- `DimEnergy DimPressure Dimensionful UnitChoices.SI` verified the likely Lean
  names used by the file.
- `WithDim Dimension.L𝓭` returned and grounded the dimension-tagged carrier and
  the length dimension used to construct physical volume.

Source, module, and docstring were fetched only for the candidates used in the
formalization: `DimEnergy`, `DimPressure`, `Dimensionful`, `UnitChoices.SI`,
`WithDim`, and `Dimension.L𝓭`.

## Physlib/Mathlib names grounded

- `DimEnergy` from `Physlib.Units.WithDim.Energy`.
- `DimPressure` from `Physlib.Units.WithDim.Pressure`.
- `Dimensionful` and `UnitChoices.SI` from `Physlib.Units.Basic`.
- `WithDim` from `Physlib.Units.WithDim.Basic`.
- `Dimension.L𝓭` from `Physlib.Units.Dimension`; it supplies the length
  dimension used three times for volume.

## Local abstractions introduced

- `VolumeQuantity` is `Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)`. This is
  a unit-independent physical volume, not a scalar placeholder.
- `ThermodynamicState` pairs physical pressure and volume.
- `ProcessLeg` and `ThermodynamicPath` retain endpoints, intermediate states,
  process kinds, and arrow directions from the image.
- `ThermodynamicModel` separates state-dependent internal energy from
  path-dependent heat and work.
- `SatisfiesFirstLaw` is a faithful local governing-law predicate because no
  suitable library-level general thermodynamic-process interface was found.

## Grounding gaps and redraft requests

- LeanExplore exposed no general first-law/thermodynamic-path API and no
  ready-made dimensionful volume type. The local abstractions above fill only
  those gaps.
- The auxiliary caption reverses/misclassifies several arrows. The Lean file
  follows the primary image as required; a future blueprint redraft should
  correct the caption to match it.
- The requested `.archon/AGENTS.md` was absent. The available
  `.archon/prover-modes/physics-formalize.md` supplied the role instructions.
- The `archon` executable was not on `PATH`, so the optional dependency-graph
  query could not be run. The blueprint contains no listed prior theorem
  dependencies, and the source report lists no previous parts.

## Verification

- `archon-lean-lsp` diagnostics: success with only the expected main-theorem
  `sorry` warning.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0340.lean`: exit code 0,
  with only the expected `sorry` warning.

## Prover result (iteration 007)

Closed the sole proof obligation,
`PhyXMiniProblems.ProblemPhyXMini0340.heatIntoSystemAlongADB_eq_45_joules`.
The proof extracts the common `stateA` and `stateB` endpoints of `pathACB` and
`pathADB` from `MatchesSuppliedFigure`, specializes `SatisfiesFirstLaw` to both
paths, rewrites the supplied heat and work values, and finishes the resulting
real-linear equations with `linarith`.

Verification:

- `archon-lean-lsp` reports no diagnostics or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0340.lean` exits with
  status 0 and no output.
- Root `lake build` completes successfully.
- The source contains no remaining `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- `lean_verify` reports no suspicious source patterns. The theorem depends
  only on the standard foundational axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- No `/- USER: ... -/` file-specific hint is present.

No redraft is needed. The theorem statement is faithful and provable as
written. The target blueprint environment was not marked `\leanok` because
the task's explicit write permissions allow edits only to the assigned Lean
file and this task-result file; the orchestrator should synchronize that mark.
