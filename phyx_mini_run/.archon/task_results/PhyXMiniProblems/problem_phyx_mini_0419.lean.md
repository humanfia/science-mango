# Autoformalization result: `problem_phyx_mini_0419.lean`

## Assumption/target split

### Governing laws

- `SatisfiesQuasiStaticBoundaryWorkLaw` states the general isobaric law
  `W_by = p (V_finish - V_start)` with the `kPa·cm³`-to-joule conversion, and
  zero boundary work for isochoric legs.  It also states the corresponding
  constant-pressure and constant-volume relations.
- `SatisfiesFirstLawAndCycleClosure` states `Q = ΔU + W_by` on every directed
  leg and `Σ ΔU = 0` over the closed cycle.
- `thermalEfficiency` is the general heat-engine definition `W_net / Q_in`,
  with `Q_in` computed by summing positive signed leg heats.

### Previous-part results

- None.  The source report has an empty `previous_parts` list.

### Problem and physical-regime assumptions

- `MatchesProblemStatement` records only that the cyclic device is a heat
  engine.
- `HasPhysicalStateReadouts` requires positive pressure and volume at all four
  corner states.

### Figure/data readouts

- `MatchesPrimaryPVDiagram` records the literal axis roles and units, the four
  corner markers, the clockwise directions and endpoints, the horizontal or
  vertical geometry, and the isobaric or isochoric role of each leg.
- The primary raster gives the exact corner readouts `(V, p)`:
  `(100 cm³, 100 kPa)`, `(100 cm³, 400 kPa)`,
  `(200 cm³, 400 kPa)`, and `(200 cm³, 100 kPa)`.
- The raster—not the contradictory auxiliary caption—shows clockwise process
  arrows.  The caption's `200 kPa` lower edge and “counterclockwise” claim were
  therefore not formalized.
- The visible outward heat arrows are attached to the right and bottom legs
  and read `-90 J` and `-25 J`.
- `HasFigureIndicatedHeatFlowPattern` makes explicit the interpretation needed
  for heat-input bookkeeping: left and top are the absorbing legs, while right
  and bottom are the rejecting legs.  It fixes no total heat input and no
  efficiency.
- The supplied answer-choice table and recorded answer label are represented
  by `displayedEfficiency` and `recordedAnswerChoice`.

### Current target conclusions

- `cycleWorkAndHeatInputReadouts` concludes, rather than assumes, that the net
  work is `30 J` and total heat input is `145 J`.
- `thermalEfficiency_eq_answerChoiceC` concludes the exact efficiency
  `6 / 29` and proves that it rounds to the displayed hundredth `0.21` for
  recorded choice C.

## Goal-faithfulness audit

No premise structure contains `30`, `145`, `6 / 29`, or an assertion that the
efficiency matches choice C.  The work law, first law, cycle closure, and heat
flow signs are general physical/modeling relations.  The only answer values in
definitions are the four literal multiple-choice readouts supplied by the
problem, and `recordedAnswerChoice := .C` is dataset metadata; neither supplies
the equality or rounding conclusion.  `thermalEfficiency` is defined by the
standard ratio of independently modeled cycle totals, not by the requested
answer.  The substantive numerical relations remain on the conclusion side of
the lemma and theorem.

## Declarations and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0419:target` is represented by
  `PhyXMiniProblems.ProblemPhyXMini0419.thermalEfficiency_eq_answerChoiceC`.
- Supporting derived declaration:
  `PhyXMiniProblems.ProblemPhyXMini0419.cycleWorkAndHeatInputReadouts`.
- Supporting model declarations include `VolumeQuantity`, calibrated unit
  readouts, cycle/state/leg vocabulary, `RectangularPVHeatEngineCycle`, the
  problem/figure predicates, physical positivity, heat-flow interpretation,
  boundary-work laws, first-law closure, cycle totals, answer choices, and the
  hundredth-rounding relation.

The blueprint theorem was not marked `\leanok` because this task's explicit
write-permission section forbids editing blueprint chapters.  A later
blueprint-authorized stage should add that marker.

## LeanExplore grounding

Queries actually run with `packages: ["Mathlib", "Physlib"]`:

- Natural language: `thermodynamic heat engine efficiency pressure volume work first law`.
- Natural language: `physical quantity SI pressure volume energy`.
- Likely name: `PhysicalQuantity`.
- Natural language: `SI unit pressure energy volume`.
- Likely names/unit searches: `DimVolume`, `DimPressure.kilopascal`,
  `centimeter cubed unit volume`, and `DimEnergy.joule`.

Candidate source/module information fetched and used:

- `DimPressure` from `Physlib.Units.WithDim.Pressure`.
- `DimPressure.pascal` from `Physlib.Units.WithDim.Pressure`.
- `DimEnergy` and `DimEnergy.joule` from
  `Physlib.Units.WithDim.Energy`.
- `Dimensionful`, `Dimension`, and `UnitChoices.SI` from Physlib's units
  infrastructure.

`LengthUnit.centimeters` was inspected but not used: it is a length unit, while
the figure requires a cubic-volume readout.  `NVEHamiltonian.pressure` and
`IdealGas.ideal_gas_law` were near-topic search results but are specialized to
models not assumed by this problem and were not used.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices.SI`,
  `DimPressure`, `DimPressure.pascal`, `DimEnergy`, and `DimEnergy.joule`.
- Core/Mathlib real operations used after import transitively supplies them:
  real arithmetic, `max`, and `abs`.

## Local abstractions introduced

- `VolumeQuantity := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)` preserves the
  physical `L³` role because LeanExplore found no dedicated Physlib
  `DimVolume` alias.
- The cycle, state/leg labels, figure annotations, thermodynamic laws, and
  heat-flow predicates are local because no matching general Physlib heat
  engine/closed-`pV`-cycle API was found.  They keep pressures, volumes, and
  energies dimensionful and expose only calibrated scalar readouts where the
  source itself supplies numbers.

## Grounding gaps and redraft requests

- LeanExplore returned no reusable general declaration for heat-engine thermal
  efficiency, the first law on a finite cycle, rectangular `pV` boundary work,
  or a dedicated dimensionful volume type.
- The optional dependency-graph navigation command could not be used because
  `archon` was not present on `PATH` in this runtime.
- The requested `.archon/AGENTS.md` file is absent.  The available
  `.archon/prover-modes/physics-formalize.md` and `.archon/PROGRESS.md` were
  read and followed instead.
- Blueprint maintainers should add `\leanok` to the target environment once a
  stage with blueprint write permission handles this chapter.

## Verification

- `archon-lean-lsp` diagnostics succeeded with only the two expected
  `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0419.lean` exited with code
  0 and emitted only those same two expected warnings.
