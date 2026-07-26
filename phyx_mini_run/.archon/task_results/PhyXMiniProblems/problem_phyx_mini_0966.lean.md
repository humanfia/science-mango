# Autoformalization result: `problem_phyx_mini_0966.lean`

## Assumption/target split

### Governing laws

- `SatisfiesCircularArcBiotSavartLaw` states the general center-field relation
  `B = μ₀ I θ / (4πR)` for each stored arc, with its vector direction supplied
  by the right-hand rule from the depicted arc-current sense.
- `SatisfiesRadialConnectorBiotSavartLaw` states that each straight radial
  connector contributes zero field at `P`, because `dℓ` is parallel to the
  displacement to the observation point.
- `SatisfiesMagneticFieldSuperposition` relates the independent total field at
  `P` to the vector sum of the four independent segment fields.
- `SatisfiesSteadyCurrentFieldModel` records time independence of the segment
  and total fields for the steady current.
- `CalibratesMagneticFluxDensityMagnitudeAtP` relates the independent
  dimensionful magnitude observable to the norm of the total Physlib field.
- `UsesStandardVacuumPermeability` calibrates the dimensionful permeability to
  the selected `Electromagnetism.EMSystem.μ₀` and to `4π × 10⁻⁷ T m/A` in SI.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesAnnularSectorProblemData` records `I = 12 A`, inner radius `20 cm`,
  outer radius `30 cm`, both connector lengths `10 cm`, and sector angle
  `2π/3` radians.
- `MatchesPrimaryAnnularSectorFigure` records labels `P,A,B,C,D`, all four
  wire segments, the `120°` marker, purple current arrows, the closed traversal
  `D → A → B → C → D`, clockwise current on inner arc `DA`, and
  counterclockwise current on outer arc `BC`.
- `HasAnnularSectorGeometry` records `P` as the common center, `A,D` on the
  inner circle, `B,C` on the outer circle, metric connector lengths, and the
  same-ray relations for `P-A-B` and `P-D-C`.
- `HasPhysicalAnnularSectorParameters` selects the positive, nondegenerate
  physical branch.

### Current target conclusions

- `totalMagneticFieldAtP_exact`: the total vector is exactly
  `(4π / (3 × 10⁶)) T` into the page.
- `problem_phyx_mini_0966`: the dimensionful magnitude reads exactly `4π/3 μT`,
  rounds to `4.19 μT`, and uniquely selects answer choice B.

## Goal-faithfulness audit

The exact vector, `4π/3 μT` magnitude, `4.19 μT` rounding conclusion, and
choice B selection occur only in the conclusions of the derived lemma/theorem
(apart from explanatory comments and the supplied answer table). The setup
stores independent segment fields, a total field, and a dimensionful magnitude
observable. None is defined using the desired answer.

The law premises contain only reusable physical relations in the stored
quantities: circular-arc Biot--Savart, radial-segment cancellation,
superposition, steady-current behavior, vacuum-permeability calibration, and
norm calibration. The answer table contains the four source-provided displayed
values, but it does not constrain the actual field and cannot prove the target
by unfolding. Thus no current target conclusion was placed in data, figure,
geometry, law, `Valid...`, or `Satisfies...` premise fields.

## Declarations created and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0966:target` corresponds to theorem
  `PhyXMiniProblems.ProblemPhyXMini0966.problem_phyx_mini_0966`.
- Auxiliary derived declaration: `totalMagneticFieldAtP_exact`.
- Physical dimensions and quantities: `electricCurrentDimension`,
  `magneticPermeabilityDimension`, `magneticFluxDensityDimension`,
  `LengthQuantity`, `ElectricCurrentQuantity`,
  `MagneticPermeabilityQuantity`, and `MagneticFluxDensityQuantity`.
- SI/display readouts: `lengthInMeters`, `lengthInCentimeters`,
  `currentInAmperes`, `permeabilityInTeslaMetersPerAmpere`,
  `magneticFluxDensityInTeslas`, and `magneticFluxDensityInMicroteslas`.
- Figure/geometry vocabulary: `FigurePoint`, `WireSegment`, `ArcSegment`,
  `RadialConnector`, `ArcCurrentSense`, `PageNormalDirection`, `FigureColor`,
  `AnnularSectorFigure`, and their segment/direction helper definitions.
- Physical model: `AnnularSectorWireSetup`,
  `MatchesAnnularSectorProblemData`, `MatchesPrimaryAnnularSectorFigure`,
  `HasAnnularSectorGeometry`, and `HasPhysicalAnnularSectorParameters`.
- Governing-law interfaces: `UsesStandardVacuumPermeability`,
  `SatisfiesSteadyCurrentFieldModel`, `SatisfiesCircularArcBiotSavartLaw`,
  `SatisfiesRadialConnectorBiotSavartLaw`,
  `SatisfiesMagneticFieldSuperposition`, and
  `CalibratesMagneticFluxDensityMagnitudeAtP`.
- Answer vocabulary: `AnswerChoice`, `displayedMagneticFieldInMicroteslas`,
  `RoundsToNearestHundredthMicrotesla`, and
  `IsUniqueClosestDisplayedAnswer`.

## LeanExplore queries and candidates used

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- Natural language: `magnetic field at center of a circular arc carrying
  electric current Biot Savart law`.
- Likely names: `Physlib electromagnetism magnetic field electric current`.
- Natural-language units: `SI units ampere tesla magnetic flux density
  electric current unit`.
- Likely unit names: `Physlib.Units ampere tesla current magneticField`.
- Natural language: `unit-independent physical quantity carrying a physical
  dimension with coherent SI readout`.
- Likely names: `Dimensionful WithDim UnitChoices.SI`.

Inspected source/module/docstring candidates:

- `Electromagnetism.MagneticField` (ID 385560), from
  `Physlib.Electromagnetism.Basic`: used as the segment and total
  spacetime-dependent vector-field type.
- `Electromagnetism.CurrentDensity` (ID 385564), from the same module:
  inspected but not used because a three-dimensional current-density field is
  not the finite steady line-current magnitude in this problem.
- `Dimensionful` (ID 394284), from `Physlib.Units.Basic`: used through
  `Dimensionful (WithDim d NNReal)` for unit-independent magnitudes.
- `UnitChoices.SI` (ID 394270), from `Physlib.Units.Basic`: used for coherent
  metre, ampere, permeability, and tesla readouts.

## Physlib/Mathlib names grounded

- Physlib: `Electromagnetism.MagneticField`, `Electromagnetism.EMSystem`,
  `Dimension`, `Dimensionful`, `WithDim`, `UnitChoices`, `UnitChoices.SI`,
  `Space`, `Time`, and the base dimensions `L𝓭`, `M𝓭`, `T𝓭`, `C𝓭`.
- Mathlib: `EuclideanSpace`, `Fin`, `NNReal`, `Real.pi`, `dist`, affine
  subtraction `-ᵥ`, scalar multiplication, vector norm, and absolute value.

## Local abstractions introduced

- The point, segment, arc, connector, arrow, and page-normal enumerations keep
  the primary figure's labels and traversal explicit rather than reducing the
  apparatus to a single scalar equation.
- `AnnularSectorWireSetup` separates dimensionful source/geometry quantities
  from Physlib vector fields and from the independent requested magnitude.
- The circular-arc and radial-connector Biot--Savart structures were introduced
  because no matching finite-wire circular-arc law appeared in LeanExplore.
  They state the physical laws directly and do not state the final numerical
  answer.
- `CalibratesMagneticFluxDensityMagnitudeAtP` bridges Physlib's currently
  untagged real-vector magnetic-field API to a unit-independent dimensionful
  flux-density magnitude without replacing that physical magnitude by `ℝ`.

## Grounding gaps and redraft requests

- LeanExplore found Physlib electromagnetic field/potential infrastructure but
  no finite line-current type and no circular-arc Biot--Savart center-field
  theorem. The local governing-law interfaces document that gap.
- The auxiliary image caption swaps several point/segment roles, while the
  prose and primary raster clearly show inner arc `DA`, outer arc `BC`, and
  radial connectors `AB` and `CD`. Following the instruction to treat the
  image as primary evidence, the Lean model uses the raster/prose geometry.
- The requested `archon dag-query` navigation could not be run because
  `archon` was not available on `PATH` in this environment. The source report
  independently confirms there are no previous parts.
- The blueprint chapter was not edited because the task's explicit write
  permissions allow edits only to this Lean file and task-result report. The
  plan/orchestration agent should add `\leanok` to
  `thm:physics:phyx_mini_0966:target` after accepting this formalization.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0966.lean` exits successfully.
The only diagnostics are the two expected `declaration uses sorry` warnings for
`totalMagneticFieldAtP_exact` and `problem_phyx_mini_0966`.

# Prover result — Archon iteration 020

This section supersedes the autoformalization-stage verification note above.

## Status

Complete. Both proof placeholders were closed without changing either
declaration signature:

- `totalMagneticFieldAtP_exact`
- `problem_phyx_mini_0966`

The auxiliary lemma derives the inner and outer radii in metres, specializes
the two circular-arc Biot--Savart hypotheses, removes both radial-connector
fields, applies superposition, and combines the opposite page-normal
directions to obtain the exact net vector.

The target theorem uses the norm calibration to obtain the exact
`4π/3 μT` magnitude. Mathlib's certified decimal bounds on `Real.pi` then
prove nearest-hundredth rounding to `4.19 μT` and strict closeness to answer B
against choices A, C, and D.

## Verification

The direct Lean check

`LEAN_PATH=<project package paths> lean PhyXMiniProblems/problem_phyx_mini_0966.lean`

exited with code 0. Diagnostics were limited to non-fatal linter warnings
about three frozen but unused hypotheses and one unused `simp` argument.
Source scanning found no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.

## Blueprint follow-up

The blueprint was not edited because this prover task explicitly grants write
permission only for the assigned Lean file and this task-result file. The
orchestration/plan agent should mark
`thm:physics:phyx_mini_0966:target` with `\leanok`.

## Redraft needed

None.
