# Autoformalization result: `problem_phyx_mini_0307.lean`

## Assumption/target split

### Governing laws

- `SatisfiesStandingWaveInterferenceLaw setup` states the symbolic interference relations
  `A_max = A + B`, `A_min = A - B`, and `SWR = A_max / A_min` using coherent SI amplitude readouts.  It contains neither the substituted `SWR = 1.50` nor the requested reflection percentage.
- `SatisfiesCommonMediumPowerReflectionLaw setup` existentially supplies a positive common-medium proportionality scale `k` and states `P_incident = k A²`, `P_reflected = k B²`, and `R = P_reflected / P_incident`.  This represents the source's squared-amplitude power proportionality without assuming `R = 1/25` or `R = 4%`.
- `HasPhysicalWaveParameters setup` records a positive incident amplitude, the smaller reflected amplitude, positive incident power and propagation speeds, and nonnegative reflected power.
- Continuity is part of each `ContinuousTravelingWave`: its dimensionless carrier profile is accompanied by a `Continuous` proof.

### Previous-part results

- None.  The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesProblemAndFigureData setup` states that the reflected component counter-propagates through the incident component and that `SWR = 3/2`, the exact rational form of `1.50`.
- The primary bitmap was inspected directly.  Its two outer arrows are represented as `leftMaximum` and `rightMaximum`, both labelled `Amax`; its middle arrow is `centralMinimum`, labelled `Amin`.  Their left-to-right order, repeated maximum-amplitude readout, and the shown smooth envelope curves are recorded.
- The figure provides no calibrated pixel-to-amplitude scale, so pixel coordinates encode only horizontal ordering.  Arrow amplitudes remain physical dimensionful quantities.
- The four displayed percentages are transcribed by `displayedReflectionPercentage` as `16/5`, `7/2`, `19/5`, and `4` for choices A through D.

### Current target conclusions

- `reflected_to_incident_amplitude_ratio` derives `B / A = 1/5`.
- `reflectionCoefficient_eq_one_twenty_fifth` derives the dimensionless power ratio `R = 1/25`.
- `problem_phyx_mini_0307` concludes `R = 1/25`, `100 R = 4`, agreement with answer D, and uniqueness of D among the displayed percentages.

## Goal-faithfulness audit

The reflection coefficient is an independent field of `BoundaryReflectionSetup`; it is not defined as `1/25` or from an answer choice.  Likewise, the incident and reflected powers and amplitudes are independent dimensionful fields.  The setup, figure/data predicate, and physical-parameter structure contain no numerical value for `R`, no `4%` statement, and no assertion selecting D.

The only numerical input relevant to the calculation is the source datum `SWR = 3/2`.  The law predicates remain symbolic in `A`, `B`, their envelope amplitudes, their powers, and the positive proportionality scale `k`.  Consequently the target amplitude ratio, power ratio, percentage, and answer selection all remain on lemma/theorem conclusion sides.  `reflectionCoefficientPercentage` is only the standard dimensionless conversion `100 * R`; it does not define that expression to equal `4`.

The arbitrary `amplitudeDimension` parameter is deliberate: the problem does not identify whether amplitude means displacement, acoustic pressure, electric field, or another physical quantity.  `WaveAmplitude amplitudeDimension`, `WavePower`, and `WaveSpeed` use Physlib's unit-independent `Dimensionful (WithDim ... NNReal)` representation rather than transparent scalar aliases.  Real numbers appear only as explicit coherent-SI readouts, dimensionless quantities, or figure coordinates.

## Declarations created and blueprint correspondence

- Dimension/quantity layer: `powerDimension`, `WaveAmplitude`, `WavePower`, `WaveSpeed`, `amplitudeSIReadout`, `powerInWatts`, and `speedInMetersPerSecond`.
- Wave/model layer: `HorizontalDirection`, `oppositeDirection`, `ContinuousTravelingWave`, and `BoundaryReflectionSetup`.
- Figure layer: `FigureArrow`, `EnvelopeLabel`, `StandingWaveEnvelopeFigure`, `maximumEnvelopeAmplitudeSI`, and `minimumEnvelopeAmplitudeSI`.
- Assumption layer: `MatchesProblemAndFigureData`, `HasPhysicalWaveParameters`, `SatisfiesStandingWaveInterferenceLaw`, and `SatisfiesCommonMediumPowerReflectionLaw`.
- Answer layer: `AnswerChoice`, `displayedReflectionPercentage`, `reflectionCoefficientPercentage`, `MatchesAnswerChoice`, and `recordedDatasetAnswer`.
- Derived declarations: `reflected_to_incident_amplitude_ratio`, `reflectionCoefficient_eq_one_twenty_fifth`, and `problem_phyx_mini_0307`.
- `problem_phyx_mini_0307` corresponds to blueprint label `thm:physics:phyx_mini_0307:target`.

## LeanExplore queries and candidates

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language physics query: `standing wave ratio reflected incident wave power reflection coefficient`.
- Wave concept query: `Wave amplitude power traveling wave`.
- Likely-name query: `StandingWaveRatio reflectionCoefficient reflectedPower incidentPower`.
- Unit/dimension query: `Physical dimensions dimensionless quantity SI unit ratio`.
- Likely unit-name query: `Dimensionful WithDim UnitChoices.SI Dimension.M𝓭 Dimension.L𝓭 Dimension.T𝓭`.
- Analysis queries: `Real.sqrt square power amplitude ratio` and `Continuous continuous function`.

Source/module information was fetched for:

- `Dimensionful` from `Physlib.Units.Basic`;
- `UnitChoices.SI` from `Physlib.Units.Basic`;
- `Dimension` from `Physlib.Units.Dimension`;
- `WithDim.val_div_val` from `Physlib.Units.WithDim.Basic`;
- `ClassicalMechanics.planeWave` from `Physlib.ClassicalMechanics.WaveEquation.Basic`;
- `ClassicalMechanics.harmonicWave` from `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave`.

The final file uses the unit infrastructure and Mathlib's `Continuous`.  `WithDim.val_div_val` grounded the behavior of same-dimension ratios, though the declarations expose ratios through named coherent-SI readouts.  `planeWave` and `harmonicWave` were inspected as near matches but not used: the former fixes a vector-valued spatial plane-wave model, while the latter fixes a harmonic cosine form.  Neither represents the source's deliberately unspecified continuous wave kind, boundary reflection, power, SWR, or envelope readouts.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimensionful`, `WithDim`, and `UnitChoices.SI`.
- Mathlib: `NNReal`, `Continuous`, and `ℝ` with its ordered-field operations.
- The power dimension is explicitly `M𝓭 * L𝓭² * T𝓭⁻³`; propagation speed is `L𝓭 * T𝓭⁻¹`.

## Local abstractions introduced

- `ContinuousTravelingWave` is the smallest local physical object needed to retain a continuous normalized profile, dimensionful amplitude and power, dimensionful speed, and propagation direction without committing to an unsupported wave species or a harmonic waveform.
- `StandingWaveEnvelopeFigure` preserves the three figure arrows and their labels while avoiding invented physical calibration from pixel lengths.
- `SatisfiesStandingWaveInterferenceLaw` is a local governing-law interface because no SWR/boundary-interference API was found.
- `SatisfiesCommonMediumPowerReflectionLaw` is an existential predicate because its SI proportionality scale is genuine model data, whereas Lean forbids non-proof fields in a `Prop`-valued structure.  It retains the scale rather than replacing the physical proportionality laws with the final squared-ratio conclusion.

## Grounding gaps and redraft requests

- LeanExplore found general Physlib plane-wave and harmonic-wave definitions but no standing-wave-ratio, boundary reflection coefficient, or common-medium amplitude-to-power API.  Faithful local abstractions were therefore required.
- The amplitude's physical dimension is absent from the source.  It is parameterized rather than guessed; a future redraft could specialize it if the intended wave species becomes known.
- The prompt-listed `.archon/AGENTS.md` is absent.  The available `.archon/prover-modes/physics-formalize.md` supplied the stage-specific role instructions.
- The `archon` executable was not available on `PATH`, so the requested DAG node/ancestor queries could not run.  The source report independently confirms there are no previous parts.
- The assigned Lean file did not previously exist, so there were no `/- USER: ... -/` hints to preserve.
- The blueprint chapter exists but was not edited with `\leanok`, because the task's explicit write permissions restrict this agent to the assigned Lean file and its task-result report.  Marker synchronization should add `\leanok` to `thm:physics:phyx_mini_0307:target`.

## Verification

- `archon-lean-lsp` diagnostics succeeded with exactly three expected `declaration uses 'sorry'` warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0307.lean` exited with code 0 and the same three expected warnings.
