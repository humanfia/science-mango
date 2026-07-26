# Autoformalization result: `problem_phyx_mini_0629.lean`

## Assumption/target split

### Governing laws

- Branch-current continuity: the resistor current and diode current equal the figure's indicated series current.
- Kirchhoff's voltage law for the source, resistor, and diode loop.
- Ohm's law for resistor `R`, together with positive resistance.
- The ideal Shockley diode equation with dimensionless exponent `q V_D / (n k_B T)` and ideality factor `n = 1`.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- Prose: diode saturation current `I_S = 5 * 10^-13 A` and temperature `T = 300 K`.
- Figure labels: `V_in`, `R`, `I`, and `V_out`.
- Figure geometry/topology: resistor and diode in the one source loop; output terminals across the diode.
- Figure orientations: positive top terminals for source/output, downward current arrow, and downward forward-current direction.
- The instantaneous input voltage and resistance are retained as physical parameters because neither has a numerical readout in the prose or image.

### Current target conclusions

- `currentInAmperes setup.indicatedCurrent = answerChoiceCurrentInAmperes .A`, i.e. the recorded `0.006 A` answer.

## Goal-faithfulness audit

The `0.006 A` value occurs only in `answerChoiceCurrentInAmperes .A` and the conclusion of `rectifier_current_matches_choice_A`. It does not occur in `MatchesStatedRectifierData`, `MatchesSuppliedHalfWaveRectifierFigure`, `IsForwardBiasedOperatingPoint`, or `SatisfiesHalfWaveRectifierLaws`. No physical field is defined by unfolding to the target value. The independent input voltage, resistance, voltage drops, and three current quantities remain fields of the operating point/components and are related only by ordinary physical laws.

The theorem is intentionally not made derivable by inventing missing values for `V_in` or `R`. Consequently, the source as supplied is underdetermined; the `sorry` is the expected autoformalization body and a later proof will require corrected source data.

## Source/law/answer audit

- **Source evidence:** the prose supplies only `I_S = 5 * 10^-13 A` and `T = 300 K`; the primary bitmap supplies the labels, terminal polarities, downward orientations, series-loop wiring, and output connection across the diode. It supplies no numerical `V_in` operating point and no numerical `R`.
- **Physical laws:** current continuity, KVL, Ohm's law, positive resistance, forward-bias sign conditions, and the ideal Shockley relation are stated independently of the answer value.
- **Recorded answer:** choice A (`0.006 A`) is retained as answer metadata and as the theorem conclusion. It is not asserted as source data or a governing law. Because the source lacks `V_in` and `R`, the recorded value is not derivable from the supplied physical model without a source correction.

## Declarations created

- Dimension and quantity layer:
  - `electricCurrentDimension`
  - `electricPotentialDimension`
  - `electricalResistanceDimension`
  - `ElectricCurrentQuantity`
  - `ElectricPotentialQuantity`
  - `ElectricalResistanceQuantity`
  - `currentInAmperes`
  - `potentialInVolts`
  - `resistanceInOhms`
  - `elementaryChargeInCoulombs`
- Physical objects and figure vocabulary:
  - `Resistor`
  - `Diode`
  - `VerticalDirection`
  - `HalfWaveRectifierFigure`
  - `HalfWaveRectifierOperatingPoint`
- Assumption interfaces:
  - `MatchesStatedRectifierData`
  - `MatchesSuppliedHalfWaveRectifierFigure`
  - `IsForwardBiasedOperatingPoint`
  - `SatisfiesHalfWaveRectifierLaws`
- Answer metadata:
  - `AnswerChoice`
  - `answerChoiceCurrentInAmperes`
- Target theorem:
  - `rectifier_current_matches_choice_A`
  - Blueprint label: `thm:physics:phyx_mini_0629:target`

## LeanExplore grounding

Queries run with `packages: ["Mathlib", "Physlib"]` included:

- `SI physical dimensions unit-independent electric current voltage resistance`
- `electric circuit Kirchhoff voltage law Ohm law Shockley diode equation`
- `Dimensionful WithDim UnitChoices.SI`
- `Temperature ofNNReal Boltzmann constant elementary charge`
- `WithDim`
- `Temperature.ofNNReal`
- `TemperatureUnit.kelvin`
- `Real.exp`

Candidates whose source and module were inspected and then used:

- `Dimension`
- `WithDim`
- `Dimensionful`
- `UnitChoices.SI`
- `Temperature`
- `Temperature.ofNNReal`
- `TemperatureUnit.kelvin`
- `Constants.kB`
- `ChargeUnit.elementaryCharge`
- `Real.exp`

The imported Physlib source was also checked locally for the exact base-dimension
names `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, `Dimension.C𝓭`, and
`Dimension.Θ𝓭`, and for the established `Dimensionful (WithDim ... )` usage
pattern.

Near-miss search results not used include `Temperature.β` (inverse temperature rather than the complete diode exponent) and electromagnetic-potential declarations (field-theory objects rather than lumped circuit quantities).

## Physlib/Mathlib names grounded

- Physlib's dimension system supplies unit-independent, dimension-tagged electrical quantities and coherent-SI evaluation.
- Physlib's `Temperature` preserves absolute-temperature nonnegativity; `Temperature.ofNNReal 300` is paired with `TemperatureUnit.kelvin` in the data predicate.
- Physlib's `Constants.kB` and `ChargeUnit.elementaryCharge` ground the physical constants in the Shockley law.
- Mathlib's `Real.exp` supplies the exponential in the Shockley relation.

## Local abstractions introduced

No lumped-element circuit or diode-law API was found. The file therefore introduces the smallest local interfaces needed to retain the physical roles:

- dimensionful current, potential, and resistance aliases over Physlib rather than aliases to `ℝ`;
- explicit resistor, diode, instantaneous operating-point, and figure structures;
- separate predicates for supplied prose data, figure readouts, forward-bias signs, and governing laws.

These abstractions preserve units, labels, topology, independent unknown quantities, and law/target separation. Real values are restricted to SI readouts, answer-choice numerals, and dimensionless factors.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration for a half-wave rectifier, lumped resistor law, Kirchhoff voltage law, or Shockley diode equation was found.
- The source is numerically underdetermined: it gives `I_S` and `T` but no instantaneous `V_in` and no `R`. The image also contains only symbolic labels. Please supply the intended input-voltage operating point and resistance (or another calibrated relation that determines them) before the prover stage.
- `.archon/AGENTS.md` was absent, and the assigned Lean file was initially absent, so there were no pre-existing protected signatures or file-specific `USER` hints to preserve. A provenance `USER` comment was added to the new Lean file.
- The requested `archon dag-query` navigation could not run because `archon` was not available on `PATH` in this session.
- The blueprint was not marked `\leanok` because the task's explicit write permissions allowed edits only to the assigned Lean file and this task-result file.

## Verification

- Lean LSP diagnostics: one expected `declaration uses sorry` warning, no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0629.lean`: exit code 0, with only the expected `sorry` warning.
