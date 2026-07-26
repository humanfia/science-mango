# Autoformalization result: `problem_phyx_mini_0877.lean`

## Review-gate response

Iteration 001 was rejected only because the available grounding preflight
predated the Lean model and no post-formalization report evidenced the searches,
grounded declarations, abstractions, gaps, or source/law/answer split. This is
the post-formalization report for the compiled declaration. The complete model
was re-audited against the source report, primary raster, and physics blueprint
in iteration 002.

## Assumption/target split

### Governing laws

- `MatchesIdealThreeCapacitorScenario` identifies all three depicted components as ideal capacitors and the left source as a battery.
- `HasPositiveCircuitCapacitances` supplies nondegeneracy for the component, intermediate parallel-branch, and total capacitances used by reciprocal laws.
- `SatisfiesIdealCapacitorCombinationLaws.parallelAdditionLaw` states that the two lower capacitances add in parallel.
- `SatisfiesIdealCapacitorCombinationLaws.seriesReciprocalLaw` states that the reciprocals of the top-capacitor and parallel-branch capacitances add for the series combination.
- Both combination laws are stated at every `UnitChoices` readout, rather than only as an untyped scalar formula.

### Previous-part results

- None. The source report has an empty `previous_parts` list, and the blueprint supplies no earlier-part result.

### Figure/data readouts

- `CapacitorLabel` names the top `10 μF`, lower-left `20 μF`, and lower-right `10 μF` capacitor symbols.
- `CircuitNode`, `BatteryTerminal`, and `MatchesSeriesParallelTopology` encode the battery-positive node, branch junction, return node, shared terminals of the lower parallel pair, and the series placement of the top capacitor.
- `ThreeCapacitorCircuitFigure` and `MatchesSuppliedThreeCapacitorFigure` encode the visible capacitor and battery symbols, plus/minus glyphs, branch split/rejoin, relative placement, printed `10`, `20`, and `10` microfarad labels, and their calibration to the dimensionful component capacitances.
- `AnswerChoice.displayedCapacitanceInMicrofarads` records choices A–D as `2.5`, `3.5`, `5.5`, and `7.5`; `recordedDatasetAnswer` records D as dataset answer-side data.

### Current target conclusions

- `capacitanceInMicrofarads setup.equivalentCapacitance = 7.5`.
- `AnswerMatchesEquivalentCapacitance setup recordedDatasetAnswer`, i.e. the derived physical equivalent capacitance agrees with displayed choice D.

## Goal-faithfulness audit

The physical `equivalentCapacitance` and intermediate `parallelBranchCapacitance` are independent fields of `ThreeCapacitorCircuitSetup`; neither is defined by the desired number or by an answer choice. The hypotheses contain only the component readouts, topology, positivity, physical component idealization, and standard series/parallel governing relations. No premise field states `7.5 μF`, selects D as physically correct, or unfolds to the target numerical equality. The value `7.5` appears as answer-choice metadata and on the conclusion side of the theorem, while the substantive first conjunct must be derived from the combination laws and figure calibrations.

The battery is retained as a figure/model component even though its voltage does not enter the ideal equivalent-capacitance calculation. Scalar real numbers are used only for explicit readouts and answer values; physical capacitances use a dimension-tagged, unit-independent quantity over `NNReal`.

## Source/law/answer audit

- **Source and figure:** the raster shows a battery, one top capacitor marked
  `10 μF`, and two lower capacitors marked `20 μF` and `10 μF`; the lower pair
  shares both endpoints, and the top component is in series with that pair.
  These observations are represented by the label, node, terminal, presentation,
  and calibration fields.
- **Physical laws:** only ideal parallel addition and ideal series reciprocal
  addition are assumed. Their fields contain no `7.5` literal and no answer
  choice.
- **Answer side:** the source metadata records choice D and all four displayed
  values. The theorem separately concludes the physically derived `7.5 μF`
  value and its agreement with that recorded choice.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0877:target` corresponds to theorem `PhyXMiniProblems.ProblemPhyXMini0877.problem_phyx_mini_0877`.
- Supporting dimension/readout declarations: `potentialDifferenceDimension`, `capacitanceDimension`, `CapacitanceQuantity`, `capacitanceReadout`, `capacitanceInFarads`, and `capacitanceInMicrofarads`.
- Supporting circuit declarations: `CapacitorLabel`, `CircuitNode`, `BatteryTerminal`, `CapacitorModel`, `VoltageSourceModel`, `ThreeCapacitorCircuitFigure`, and `ThreeCapacitorCircuitSetup`.
- Supporting premise declarations: `MatchesIdealThreeCapacitorScenario`, `MatchesSeriesParallelTopology`, `MatchesSuppliedThreeCapacitorFigure`, `HasPositiveCircuitCapacitances`, and `SatisfiesIdealCapacitorCombinationLaws`.
- Supporting answer declarations: `AnswerChoice`, `AnswerChoice.displayedCapacitanceInMicrofarads`, `recordedDatasetAnswer`, and `AnswerMatchesEquivalentCapacitance`.

The theorem body is deliberately `by sorry`, as required for the `autoformalize` / `physics-formalize` stage. `lake env lean PhyXMiniProblems/problem_phyx_mini_0877.lean` exits successfully with only the expected declaration-uses-`sorry` warning.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query `electrical capacitance capacitors connected in series and parallel capacitance units`: no capacitor-network declaration was returned; results were unrelated category-theory parallel-pair declarations and general charge/dimension declarations.
- Likely-name query `Capacitance farad microfarad SI unit capacitor`: found `UnitChoices.SI` and other general unit-system declarations, but no capacitance or capacitor-combination API.
- Likely-name query `Dimensionful`: used candidate `Dimensionful` (id 394284), with `Dimension` (id 394292) also inspected.
- Likely-name query `WithDim`: used candidate `WithDim` (id 394425).
- Likely-name query `UnitChoices.SI`: used candidate `UnitChoices.SI` (id 394270).
- Likely-name query `NNReal nonnegative real numbers`: used candidate `NNReal`
  (id 211536).
- Source, module, and docstring data were fetched for the five intended
  candidates `Dimensionful`, `Dimension`, `WithDim`, `UnitChoices.SI`, and
  `NNReal` before finalizing this report.

## PhysLean/Mathlib names grounded

- `Dimensionful` from `Physlib.Units.Basic`: a unit-choice-indexed quantity satisfying dimensional scaling.
- `Dimension` from `Physlib.Units.Dimension`, including the imported base-dimension notation `L𝓭`, `T𝓭`, `M𝓭`, and `C𝓭`.
- `WithDim` from `Physlib.Units.WithDim.Basic`: attaches a physical dimension to an underlying value type.
- `UnitChoices` and `UnitChoices.SI` from `Physlib.Units.Basic`; the latter fixes metres, seconds, kilograms, coulombs, and kelvin.
- Mathlib `NNReal` from `Mathlib.Data.NNReal.Defs` provides the nonnegative
  scalar carried by the dimensionful capacitance; `ℝ` provides named-unit
  scalar readouts.

## Local abstractions introduced

- `potentialDifferenceDimension` and `capacitanceDimension` express voltage as `M L² T⁻² C⁻¹` and capacitance as `C / V` using Physlib dimensions.
- `CapacitanceQuantity` is `Dimensionful (WithDim capacitanceDimension NNReal)`, not a transparent alias or one-field wrapper around `ℝ`; it preserves nonnegativity, dimensional role, and unit independence.
- Circuit labels, node labels, terminal maps, and figure-readout structures preserve the primary raster's component roles and connectivity.
- The two capacitor-combination equations are local governing-law fields because no matching library API was found. They express the physical parallel and series laws directly and do not contain the requested numerical result.

## Grounding gaps and redraft/process notes

- LeanExplore exposed no ready-made capacitance/farad/microfarad type and no ideal-capacitor series/parallel network law in Mathlib or Physlib. The local dimensionful quantity and explicit governing-law interface fill that gap without reducing physical capacitance to a scalar alias.
- The `archon` executable was not available on `PATH` in this runtime, so DAG queries could not be run. The source report independently confirms there are no previous parts.
- `.archon/AGENTS.md` is absent in the current project checkout. The supplied task prompt and `.archon/prover-modes/physics-formalize.md` were followed as the available role instructions.
- The blueprint environment was not edited to add `\leanok`, because the task's final write-permission section expressly forbids blueprint edits and permits changes only to the assigned Lean file and this report. The orchestrator/plan agent should add the marker after accepting the declaration.
- The gate reason requested evidence rather than a different theorem statement;
  after re-auditing the complete statement, no additional physics-model redraft
  was necessary.

## Verification

- `archon-lean-lsp` diagnostics report exactly one expected warning:
  `declaration uses sorry` on `problem_phyx_mini_0877`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0877.lean` exits with code
  0 and the same single expected warning.
