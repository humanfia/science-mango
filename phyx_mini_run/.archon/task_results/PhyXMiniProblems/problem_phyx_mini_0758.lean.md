# Prover result: `problem_phyx_mini_0758.lean`

## Outcome

- Closed both `sorry` placeholders in
  `PhyXMiniProblems.ProblemPhyXMini0758.tibiaTensionToWeightRatio_exact`
  and `PhyXMiniProblems.ProblemPhyXMini0758.problem_phyx_mini_0758`.
- Preserved both declaration signatures and every physical hypothesis.
- No redraft is needed.

## Proof

The exact-ratio lemma specializes the vertical-component and equilibrium laws
to SI readouts. Equality of all six independently represented tibia tensions
turns the finite equilibrium sum into

`6 * T * sin (degreesToRadians 40) = W`.

Positivity of `T` and `W` proves the sine factor is positive, so legitimate
cross multiplication yields

`T / W = 1 / (6 * sin (degreesToRadians 40))`.

For the displayed answer, the proof derives `3.1 < π < 3.15` from sine/cosine
Taylor bounds, then applies `Real.sin_bound`, `Real.cos_bound`, and the
double-angle identity at `x = π / 9`. This gives the certified enclosure

`100 / 159 ≤ sin (degreesToRadians 40) ≤ 100 / 153`.

Taking positive reciprocals proves that the exact tension-to-weight ratio lies
between `0.255` and `0.265`, exactly the half-hundredth tolerance around
recorded choice C (`0.26`).

## Final verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0758.lean`: passed with no
  errors or warnings.
- `lake build`: passed (`Build completed successfully (4 jobs)`).
- `lean_verify` on both declarations: no source-scan warnings; only the
  standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
- The assigned source contains no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.

## Blueprint marker

The lemma and theorem environments are ready for `\leanok`. The prover did not
edit the blueprint chapter because this lane's write permissions explicitly
restrict edits to the assigned Lean file and this task-result file; the marker
sync or plan agent should apply the markers.

## Earlier autoformalization record

The remainder of this file is the preserved modeling/grounding report. Its
closing pre-proof verification is superseded by the final verification above.

## Assumption/target split

### Governing laws

- `SatisfiesHangingStaticsLaws.weightLaw` states the general magnitude law
  `W = m g` in every coherent `UnitChoices` system.
- `SatisfiesHangingStaticsLaws.tibiaVerticalComponentLaw` states that the
  upward component supplied by each inclined tibia is `T * sin θ` in every
  coherent unit system.
- `SatisfiesHangingStaticsLaws.staticVerticalEquilibrium` states that the sum
  of the six upward tibia components equals the insect's weight.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure/data readouts

- `InsectLeg` gives six named legs: left/right fore, middle, and hind.
- `MatchesProblemData` records a horizontal rod, `θ = 40°`, horizontal leg
  sections nearest the body, and equal tibia-tension magnitudes.
- `MatchesPrimaryFigure` records the visible rod, tibia, leg joint, theta arc,
  proximal section, and insect body; the printed-label attachments; both
  representative tibiae running upward from a joint to the rod; the theta arc
  on the left; and the `Tibia` text on the right.
- `HasPhysicalHangingParameters` records positivity and the acute-angle
  nondegeneracy conditions required for division by the weight and use of the
  inclined-component law.

### Current target conclusions

- `tibiaTensionToWeightRatio_exact` concludes, for each of the six legs,
  `T / W = 1 / (6 * sin (40°))`.
- `problem_phyx_mini_0758` concludes both that exact relation and agreement,
  within half of one hundredth, with recorded choice C (`0.26`).

## Goal-faithfulness audit

The setup stores mass, gravitational acceleration, weight, six tibia-tension
magnitudes, and six vertical-support magnitudes independently. The ratio
definition is their genuine dimensionless quotient; it does not assign the
requested value. Equal tension is supplied by the prose, but neither it nor
any premise relates tension directly to weight. The three mechanics-law fields
are general physical relations and contain neither `1 / (6 sin 40°)` nor
`0.26`. The displayed answer table and the matching predicate are used only on
the conclusion side. `degreesToRadians` is only the standard angle-unit
conversion and does not encode a statics result. Thus no current target was
placed in a hypothesis, premise structure, law structure, or target-making
local definition.

## Declarations created and blueprint labels

- Physical dimensions and quantities: `accelerationDimension`,
  `forceDimension`, `MassQuantity`, `AccelerationQuantity`, `ForceMagnitude`.
- Coherent-unit readouts: `nonnegativeReadout`, `massInKilograms`,
  `accelerationInMetersPerSecondSquared`, `forceInNewtons`.
- Geometry and labels: `degreesToRadians`, `InsectLeg`, `BodySide`,
  `SegmentOrientation`, `FigureFeature`, `FigureLabel`,
  `expectedLabelTarget`, `SuppliedHangingInsectFigure`.
- Physical model and assumption interfaces: `HangingInsectSetup`,
  `MatchesProblemData`, `MatchesPrimaryFigure`,
  `HasPhysicalHangingParameters`, `SatisfiesHangingStaticsLaws`.
- Answer-side declarations: `tibiaTensionToWeightRatio`, `AnswerChoice`,
  `displayedRatio`, `recordedAnswerChoice`, `MatchesDisplayedRatioAnswer`.
- Derived helper: `tibiaTensionToWeightRatio_exact`.
- Blueprint label `thm:physics:phyx_mini_0758:target` corresponds to
  `problem_phyx_mini_0758`.

## LeanExplore queries and candidates used

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- `physical force quantity tension weight mass acceleration SI units mechanics`
  found `UnitChoices.SI` and the dimensional Newton-law examples.
- `Force Mass acceleration dimensional quantity SI` found
  `UnitExamples.NewtonsSecondWithDim` and `UnitChoices.SI`.
- `angle in degrees radians sine Real.sin pi` found `Real.sin` and
  `Real.Angle.sin`; `Real.sin` was selected because the model stores an
  explicit radian readout.
- `static equilibrium sum of forces force balance` found fluid momentum and
  unrelated balancing APIs, but no rigid-body statics interface suitable for
  this problem.
- `Quantity with physical dimensions unit system`, `UnitChoices.SI Quantity`,
  and `MeasurementSystem Quantity` found `Dimensionful`.
- `WithDim` and `WithDim physical dimension tagged real addition
  multiplication division` found `WithDim` and its value/multiplication and
  division support.
- `force dimension mass length time inverse WithDim` found the dimension
  primitives including `Dimension.L𝓭` and `Dimension.T𝓭`.

Source/module/docstring details were fetched for `Dimensionful`,
`UnitChoices.SI`, `UnitExamples.NewtonsSecondWithDim`, `Real.sin`, `WithDim`,
`WithDim.withDim_hMul_val`, `WithDim.val_div_val`, `Dimension.L𝓭`, and
`Dimension.T𝓭`. The Newton-law example was inspected as a near match but was
not used directly because it is an example over individual `WithDim` values,
whereas the present model needs unit-independent quantities and six-leg static
balance.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`,
  `Dimension.M𝓭`, `Dimension.T𝓭`, `UnitChoices`, and `UnitChoices.SI`.
- Mathlib: `Real.sin`, `Real.pi`, `NNReal`, finite sums via `BigOperators`, and
  derived `Fintype` instances for finite inductive labels.

## Local abstractions introduced

- `ForceMagnitude`, `MassQuantity`, and `AccelerationQuantity` are aliases of
  Physlib dimension-tagged, unit-independent quantities rather than aliases
  of `ℝ`; this preserves the mass, acceleration, and force roles.
- `SuppliedHangingInsectFigure` is the smallest local qualitative interface
  needed to retain the primary raster's labels and incidences.
- `HangingInsectSetup` keeps the physical quantities independent.
- `SatisfiesHangingStaticsLaws` is local because no matching general statics
  API was found. It preserves the actual weight, component, and equilibrium
  laws rather than assuming the requested ratio.
- `MatchesDisplayedRatioAnswer` uses a half-unit-in-the-last-place tolerance
  because the exact trigonometric ratio is approximately, but not identically,
  the displayed two-decimal value `0.26`.

## Grounding gaps and redraft requests

- LeanExplore exposed no suitable insect/rigid-body static-equilibrium API;
  the faithful local law interface above fills that gap.
- No degree-valued angle type matching the desired explicit `Real.sin` radian
  readout was selected, so the transparent standard conversion
  `degreesToRadians x = x * π / 180` is local.
- The `archon` executable advertised for DAG navigation was not available on
  `PATH`, so no dependency-graph result could be consulted.
- `.archon/AGENTS.md` was absent at the supplied path. The available
  `.archon/prover-modes/physics-formalize.md` and the user-provided role text
  were followed instead.
- The chapter's theorem environment was not marked `\leanok` because the task's
  write-permission section explicitly forbids editing blueprint chapters. The
  orchestration/plan agent should add `\leanok` to
  `thm:physics:phyx_mini_0758:target`.

## Verification

- `archon-lean-lsp` diagnostics: only two expected `declaration uses sorry`
  warnings, at the exact-ratio lemma and target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0758.lean`: exit code 0,
  with the same two expected `sorry` warnings and no errors.
