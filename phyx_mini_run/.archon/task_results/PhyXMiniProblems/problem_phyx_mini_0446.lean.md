# Autoformalization result: `problem_phyx_mini_0446.lean`

## Assumption/target split

### Governing laws

- `SatisfiesClosedWaterThermodynamics` states initial saturation equilibrium,
  the saturated-mixture quality law
  `v = v_f + x (v_g - v_f)`, the closed-system relation `V = m v` at every
  state, and the final equilibrium-water property-table relation.
- `SatisfiesSpringLoadedPistonMechanics` states circular piston area,
  constant pressure before spring contact, zero compression at contact,
  `ΔV = A Δz`, Hooke's law `F = k Δz`, and the differential quasistatic force
  balance `(P - P_contact) A = F` after contact.
- `SatisfiesLocalSuperheatedTableInterpolation` states strict increase of
  specific volume with temperature at the target pressure and linear
  interpolation between adjacent `600 °C` and `700 °C` table rows.
- `HasPhysicalParameters` supplies only positivity, nonnegativity, and the
  physical quality interval.

### Previous-part results

- The source report lists no previous parts.
- `targetSpecificVolume_lies_between_referenceRows` and
  `targetTemperature_lies_between_referenceRows` are new derived conclusions,
  not theorem premises. They expose the intended future proof route.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure` records water/H₂O, vertical piston motion,
  a linear spring, `105 °C`, quality `0.85`, `1 L`, first spring contact at
  `1.5 L`, piston diameter `150 mm`, spring stiffness `100 N/mm`, and the
  queried event pressure `200 kPa`.
- The inspected raster contributes only topology: cylinder, upper support,
  coil spring above the piston, piston above the water, H₂O label, and dashed
  boundary around the water. It contains no numerical labels.
- `MatchesRoundedReferenceWaterData` records rounded saturation data at
  `105 °C` and independent superheated-water rows at `200 kPa`, `600 °C` and
  `700 °C`. No row or field contains `641 °C`.

### Current target conclusions

- `final_temperature_matches_recorded_answer_D` concludes that the physical
  temperature at the `200 kPa` state is within `2 °C` of the displayed
  `641 °C` choice and that D is the unique displayed choice within this
  tolerance.
- The tolerance represents rounded steam-table data/interpolation. A numeric
  sanity check of the encoded readouts gives approximately `640.85 °C`.

## Goal-faithfulness audit

- The independent field `waterTemperature .targetPressure` is never defined
  from an answer choice or from `641`.
- Neither `MatchesProblemAndPrimaryFigure`, the reference-data structure, nor
  any governing-law structure assumes the final temperature, answer D, the
  `2 °C` match predicate, or answer uniqueness.
- `200 kPa` occurs as the event condition posed by the question, not as the
  requested temperature answer.
- The only premise narrowing the final state thermodynamically is the stated
  phase classification `superheatedVapor`; the `600–700 °C` bracket is itself
  the conclusion of a helper lemma rather than an assumption.
- `TemperatureMatchesDisplayedChoice` is a genuine absolute-error predicate;
  unfolding it does not prove that any choice matches.
- No physical primitive was collapsed to `ℝ`. Scalar reals are restricted to
  named unit readouts and the dimensionless vapor quality.

## Declarations and blueprint labels

- Blueprint `thm:physics:phyx_mini_0446:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0446.final_temperature_matches_recorded_answer_D`.
- Supporting declarations include dimensionful quantity types and readouts,
  `SpringLoadedPistonFigure`, `EquilibriumWaterPropertyTable`,
  `SpringLoadedWaterCylinder`, the six premise structures, the two bracket
  lemmas, `AnswerChoice`, and `TemperatureMatchesDisplayedChoice`.
- The blueprint chapter was not edited to add `\leanok`, because the explicit
  task write permissions allow edits only to the assigned Lean file and this
  task-result file. The coordinator should add the marker after review.

## LeanExplore queries and candidates

Queries were run with `packages: ["Mathlib", "Physlib"]`, including:

- `dimensionful physical quantity pressure volume temperature`
- `Dimensionful WithDim Temperature Pressure Volume`
- `thermodynamic state saturated water vapor quality specific volume`
- `linear spring piston pressure force area Hooke law`
- `DimTemperature`, `DimVolume`, `DimLength`
- `WithDim UnitChoices temperature kelvin`
- `Dimension.Θ𝓭 temperature base dimension`
- `DimArea physical area`
- `UnitChoices.SI`

Candidates whose source/module were fetched and used:

- `Dimensionful` (id `394284`), `Physlib.Units.Basic`
- `UnitChoices` (id `394255`) and `UnitChoices.SI` (id `394270`),
  `Physlib.Units.Basic`
- `DimPressure` (id `394474`), `Physlib.Units.WithDim.Pressure`
- `DimArea` (id `394411`), `Physlib.Units.WithDim.Area`
- `Dimension` (id `394292`), `Physlib.Units.Dimension`

Near misses checked but not used:

- `FluidDynamics.FluidState` models spatial density and velocity fields, not
  an equilibrium saturated/superheated water state.
- Physlib `Temperature` is a nonnegative scalar in an arbitrary zero-
  preserving unit. The file instead uses `Dimensionful (WithDim Θ𝓭 ℝ)` so SI
  kelvin readout and the affine Celsius offset are explicit.
- `ClassicalMechanics.HarmonicOscillator.force_eq_linear` is a one-dimensional
  oscillator force lemma; it does not express piston pressure balance or the
  dimensionful spring law needed here.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `L𝓭`, `M𝓭`, `T𝓭`, `Θ𝓭`,
  `UnitChoices.SI`, `DimArea`, and `DimPressure`.
- Mathlib: `Real.pi`, real absolute value `abs`, finite inductive types, and
  ordinary real order/arithmetic used in readout-level laws.

## Local abstractions introduced

- `EquilibriumWaterPropertyTable` is the smallest local interface found for
  saturation pressure, saturated liquid/vapor specific volume, and
  superheated specific volume. Its inputs and outputs remain dimensionful.
- `SpringLoadedWaterCylinder` keeps water state functions, closed mass,
  piston geometry, spring quantities, table rows, and figure evidence as
  independent fields.
- The local figure and law structures separate raster readouts from physical
  laws and from the answer target.
- `VolumeQuantity`, `MassQuantity`, `TemperatureQuantity`, `ForceQuantity`,
  `SpringStiffnessQuantity`, and `SpecificVolumeQuantity` use Physlib's
  dimension system because no more specialized ready-made types were found.

## Grounding gaps and redraft requests

- The requested `.archon/AGENTS.md` is absent. The stage-specific
  `.archon/prover-modes/physics-formalize.md` and supplied role instructions
  were used instead.
- The blueprint exists and is marked `% archon:physics`, but it contains only
  a generic autoformalization directive, not the promised informal numerical
  proof or a cited water-property table. The plan agent should add the
  saturation/table values and interpolation derivation, ideally with an
  authoritative source, then add `\leanok` after signature review.
- LeanExplore exposed no saturated-water quality or steam-table API in
  Mathlib/Physlib. This is why the typed local property-table interface was
  necessary.
- An attempted authoritative web lookup was blocked by access enforcement, so
  the rounded reference rows remain explicit model assumptions rather than
  externally cited constants.
- `archon dag-query` could not be run because `archon` was not available on
  `PATH`; no dependency declarations were imported from the blueprint DAG.

## Verification

- `archon-lean-lsp` diagnostics: no errors; exactly three expected `sorry`
  warnings for the two helper lemmas and the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0446.lean`: exit code `0`
  with the same three expected warnings.
