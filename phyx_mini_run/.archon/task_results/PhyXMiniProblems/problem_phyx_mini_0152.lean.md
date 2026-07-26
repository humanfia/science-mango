# Autoformalization result: `problem_phyx_mini_0152.lean`

## Assumption/target split

### Governing laws

- `HasVacuumReferenceIndex`: the evacuated cell has refractive index `1`.
- `ObeysGasCellOpticalPathLaw`: filling the unchanged glass cell increases the optical path by the traversal count times the cell depth times `n_final - n_vacuum`.
- `ObeysFringeCountingLaw`: the accumulated optical-path increase equals the counted number of fringe passages times the vacuum wavelength.
- `HasPhysicalParameters`: the physical lengths and refractive indices are positive, the path increase is nonnegative, and filling the cell does not decrease its refractive index.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- `HasStatedReadouts`: cell interior depth `1.155 cm`, vacuum wavelength `632.8 nm`, `158` dark fringes, observed at the reference line.
- `MatchesSourceFigure`: source, splitting mirror `M_S`, glass container, and `M_2` lie in that left-to-right order on the horizontal arm; the `M_1` arm is vertical; `M_S` is at 45 degrees; the drawn arrow directions are recorded; and the outbound and returning `M_2` legs cross the cell, yielding two cell traversals.
- The figure was inspected directly at `phyx_data/test_image/152.png`; the return arrow through the container is the primary evidence for the factor of two.

### Current target conclusions

- `finalRefractiveIndex_eq_exact`: the final gas index is exactly `2071427 / 2062500`.
- `problem_phyx_mini_0152`: the same exact index holds and its nearest-millionth display is answer choice C, `1.004328`.
- The exact value is approximately `1.0043282424`; the theorem deliberately treats `1.004328` as a rounded display rather than as an exact equality.

## Goal-faithfulness audit

No hypothesis or setup field contains either `2071427 / 2062500`, `1.004328`, or answer choice C. The setup contains an unknown dimensionless refractive-index readout at the evacuated and final-density states. The only numeric premises are the problem's measured values, the vacuum reference index, and figure-derived geometry. The two physical predicates state independent optical-path laws, not the requested answer. `answerRefractiveIndex` merely transcribes all four printed choices, while `IsNearestMillionthReadout` states a general rounding relation.

The factor of two is present only as a figure-derived traversal count: the image shows the `M_2` arm crossing the cell outbound and on return. The exact index and the selection of C remain conclusions requiring derivation from the readouts and governing laws.

## Declarations created

- Physical/unit layer: `LengthQuantity`, `lengthInMeters`, `lengthInCentimeters`, `lengthInNanometers`.
- States and figure labels: `CellState`, `FigureElement`, `BeamLeg`, `PropagationDirection`.
- Experiment model: `GasCellInterferometer`.
- Premise predicates: `HasStatedReadouts`, `MatchesSourceFigure`, `HasPhysicalParameters`, `HasVacuumReferenceIndex`, `ObeysGasCellOpticalPathLaw`, `ObeysFringeCountingLaw`.
- Answer/rounding layer: `AnswerChoice`, `answerRefractiveIndex`, `IsNearestMillionthReadout`.
- Derived declarations: `finalRefractiveIndex_eq_exact` and `problem_phyx_mini_0152`.
- Blueprint label `thm:physics:phyx_mini_0152:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0152.problem_phyx_mini_0152`.

## LeanExplore queries/candidates actually used

All LeanExplore calls used package filters `Mathlib` and `Physlib`.

- Query `interferometer gas cell fringe shift optical path length refractive index`: no matching interferometer/fringe-shift optics declaration; returned unrelated path and ideal-gas candidates.
- Query `refractive index optical path difference`: no physical refractive-index or optical-path API; returned unrelated topological-path declarations.
- Query `Dimensionful WithDim physical length SI centimeters nanometers`: selected `Dimensionful`, `UnitChoices.SI`, `LengthUnit.centimeters`, `LengthUnit.nanometers`, and `Dimension.L𝓭`.
- Query `LengthUnit.nanometers LengthUnit.centimeters`: confirmed both concrete length-unit declarations.
- Query `WithDim`: selected the dimension-tagging structure `WithDim`.

Source, module, and docstring data were fetched for all six selected LeanExplore declarations. Their modules are `Physlib.Units.Basic`, `Physlib.SpaceAndTime.Space.LengthUnit`, `Physlib.Units.Dimension`, and `Physlib.Units.WithDim.Basic`.

## Grounded Mathlib/Physlib names

- `Dimensionful`
- `WithDim`
- `Dimension.L𝓭`
- `UnitChoices.SI`
- `LengthUnit.centimeters`
- `LengthUnit.nanometers`

The imports are explicitly `Mathlib` (to ensure elaboration in the project's real Mathlib environment, addressing the iteration-001 review reason) and `Physlib.Units.WithDim.Basic` (which supplies these physical-unit definitions and their re-exports).

## Local abstractions introduced

- `GasCellInterferometer` keeps physical lengths as Physlib `Dimensionful` quantities and stores only the dimensionless refractive index as a real-valued ratio.
- `CellState` separates the initially evacuated cell from gas at final density without building either index value into the type.
- Figure enums and `MatchesSourceFigure` preserve labels, placement, arrow directions, mirror orientations, and the physical double traversal visible in the image.
- The optical-path and fringe-counting predicates are faithful local governing-law interfaces because LeanExplore found no interferometer or refractive-index model in Mathlib/Physlib.
- `IsNearestMillionthReadout` is needed because the given choice is a six-decimal rounding of the exact value.

## Verification

- Iteration-001 rejection addressed: the file now explicitly imports `Mathlib` in addition to its Physlib unit module.
- Lean LSP diagnostics: only the two expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0152.lean`: exit code 0, with only those two warnings.
- Independent `norm_num` checks confirmed both the exact rational calculation and the nearest-millionth error bound for choice C.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration modeling refractive index, gas-cell interferometry, optical-path fringe shifts, or this figure geometry was found, so the faithful local abstractions above are necessary.
- The `archon` executable advertised for DAG queries was not available on this process's `PATH`, so no dependency-graph result could be obtained. The chapter and source report list no previous-part dependencies.
- The assigned Lean file contains no file-specific `/- USER: ... -/` comment.
- The current blueprint theorem environment has no `\lean{...}` reference. An authorized blueprint/sync agent should associate it with `PhyXMiniProblems.ProblemPhyXMini0152.problem_phyx_mini_0152` and apply the appropriate `\leanok` marker. This prover did not edit the chapter because the task's write-permission section restricts writes to the assigned Lean file and this result file.
- `.archon/AGENTS.md` was absent in this checkout. The active `.archon/prover-modes/physics-formalize.md` and the injected role instructions were followed instead.
