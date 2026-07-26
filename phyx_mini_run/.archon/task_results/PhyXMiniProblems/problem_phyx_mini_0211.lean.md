# Autoformalization result: `problem_phyx_mini_0211.lean`

## Assumption/target split

### Governing laws

- `SatisfiesEchoPropagationLaws.constantSpeedPropagation` states
  `distance = speed × time` separately for the outbound and reflected-return
  air legs.
- `SatisfiesEchoPropagationLaws.roundTripTimeComposition` states that the
  emission-to-detection duration is the sum of those two leg durations.
- `HasPhysicalEchoParameters` requires a positive camera-subject separation,
  ultrasonic frequency, sound speed, and leg lengths, together with
  nonnegative leg and round-trip durations.
- `UsesStandardAirSoundSpeed` supplies the separate textbook calibration
  `340 m/s`. The source does not print a sound speed or air temperature, so
  this was not folded into either the primary-image predicate or the generic
  propagation law.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- The primary raster was inspected. It places the camera at the left and the
  photographed subject at the right. Oppositely directed green arrows show an
  outgoing camera-to-subject leg and a subject-to-camera return leg.
- `FigureObject` preserves the camera body, ultrasonic emitter, return sensor,
  and photographed subject as separate physical roles. `PulseLeg` preserves
  the outbound and reflected-return routes.
- `MatchesPrimaryFigure` records that the emitter and sensor are co-located
  with the camera; the subject is to the right; the subject is the reflector;
  each leg has the one-way separation as its path length; the two propagation
  directions are opposite; and the sensor detects the returned pulse.
- `HasStatedObjectDistance` records the problem's one-way separation as
  `20 m`.
- `EmitsUltrasonicPulse` records the stated high-frequency character using the
  conventional ultrasonic lower edge of `20 kHz`.
- `AnswerChoice.milliseconds` transcribes all four displayed values: A `180
  ms`, B `160 ms`, C `140 ms`, and D `120 ms`.
- `recordedDatasetAnswer` transcribes the supplied metadata label D.

### Current target conclusions

- `roundTripTravelTime_milliseconds_eq` concludes that the idealized model's
  unrounded round-trip duration is exactly `2000/17 ms` (approximately
  `117.65 ms`).
- `roundTripTravelTime_matches_recordedChoiceD` concludes that this physical
  duration is uniquely closest to recorded choice D, `120 ms`, among the four
  displayed values.

## Goal-faithfulness audit

`AutofocusEchoSetup.roundTripTravelTime` and both values of
`AutofocusEchoSetup.legTravelTime` are unconstrained dimensionful physical
durations. No setup field, scenario predicate, calibration predicate,
positivity predicate, or propagation-law field assigns any of them `120 ms`
or `2000/17 ms`, and none asserts that D is closest.

The propagation premise is a generic two-leg constant-speed law plus duration
additivity. It contains the unknown travel time but no derived numerical
answer. The `20 m` separation and `340 m/s` speed are independent distance and
environmental calibration data; obtaining the result still requires using
both pulse legs, solving the propagation equations, converting seconds to
milliseconds, and comparing all four choices.

`recordedDatasetAnswer` and `AnswerChoice.milliseconds` only transcribe the
provided metadata and answer table. Unfolding them does not determine the
unknown physical duration or prove the closest-choice inequality. Thus neither
current target conclusion was smuggled into a premise or into a definition
that makes the theorem true by unfolding.

## Declarations created and blueprint correspondence

- Dimensionful roles: `AcousticLength`, `AxialPosition`,
  `AcousticDuration`, `AcousticFrequency`, and `AcousticSpeed`.
- Named-unit readouts: `lengthReadout`, `positionReadout`, `durationReadout`,
  `frequencyReadout`, `speedReadout`, and their metre, second, millisecond,
  hertz, and metre-per-second specializations.
- Figure labels and apparatus: `FigureObject`, `PulseLeg`, `AxialDirection`,
  and `AutofocusEchoSetup`.
- Figure/data and physical premises: `MatchesPrimaryFigure`,
  `HasStatedObjectDistance`, `IsUltrasonic`, `EmitsUltrasonicPulse`,
  `UsesStandardAirSoundSpeed`, and `HasPhysicalEchoParameters`.
- Governing-law interface: `SatisfiesEchoPropagationLaws`.
- Answer data and comparison: `AnswerChoice`,
  `AnswerChoice.milliseconds`, `recordedDatasetAnswer`, and
  `IsClosestAnswerChoice`.
- Derived declarations: `roundTripTravelTime_milliseconds_eq` and
  `roundTripTravelTime_matches_recordedChoiceD`.
- Blueprint label `thm:physics:phyx_mini_0211:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0211.roundTripTravelTime_matches_recordedChoiceD`.
  The exact-duration lemma exposes the unrounded intermediate result for the
  later physics prover.

The blueprint chapter was not edited because the task's explicit write
permissions restrict edits to the assigned Lean file and this task-result
file. The coordinator should add the theorem's `\lean{...}` annotation and
`\leanok` to the existing theorem environment.

## LeanExplore queries/candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Query `acoustic pulse reflected round trip travel time distance speed of
  sound` returned `UnitExamples.SpeedEq` as the only relevant physical-law
  candidate; no acoustic echo or reflected-pulse API appeared.
- Query `travel time equals distance divided by speed` again returned
  `UnitExamples.SpeedEq` and also `DimSpeed`.
- Query `Dimensionful WithDim length duration speed TimeUnit milliseconds`
  returned `Dimensionful`, `TimeUnit.milliseconds`,
  `UnitExamples.SpeedEq`, and related unit declarations.
- Likely-name query `DimSpeed` returned `DimSpeed` and its standard-speed
  constructors.

Source and module details were fetched for the candidates actually used to
design the model:

- `UnitExamples.SpeedEq` (id 394344), from `Physlib.Units.Examples`, states
  the dimensionally typed relation `s = d/t` for individual `WithDim` values.
- `Dimensionful` (id 394284), from `Physlib.Units.Basic`, represents quantities
  coherently across choices of physical units.
- `TimeUnit.milliseconds` (id 393635), from
  `Physlib.SpaceAndTime.Time.TimeUnit`, is defined as `10⁻³` seconds.
- `DimSpeed` (id 394481), from `Physlib.Units.WithDim.Speed`, is the
  nonnegative unit-independent length-per-time quantity used directly for the
  speed of sound.

The Lean LSP's local declaration search independently verified
`Dimensionful` and `DimSpeed`; final diagnostics validated the remaining unit
names and readout syntax in context.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `DimSpeed`, `UnitChoices.SI`, `LengthUnit.meters`, `TimeUnit.seconds`, and
  `TimeUnit.milliseconds`, imported through
  `Physlib.Units.WithDim.Speed`.
- Mathlib/Lean numeric infrastructure: `NNReal` for nonnegative physical
  magnitudes, `ℝ` for signed positions and named-unit readouts, absolute value,
  inequalities, finite inductive labels, and exact rational expressions.

## Local abstractions introduced

- `AcousticLength`, `AcousticDuration`, and `AcousticFrequency` compose
  Physlib's `Dimensionful` and `WithDim` APIs with the appropriate dimensions;
  they are not transparent scalar aliases.
- `FigureObject`, `PulseLeg`, and `AxialDirection` preserve the physical
  apparatus roles and the primary image's out-and-back route rather than
  collapsing the problem to a scalar equation.
- `AutofocusEchoSetup` keeps the unknown physical time, per-leg paths,
  per-leg times, pulse frequency, sound speed, emitter, reflector, detector,
  and detection event distinct.
- `SatisfiesEchoPropagationLaws` is the smallest route-aware governing-law
  interface needed because the available dimensional example does not model
  unit-independent acoustic paths, reflection, or total echo time.
- `IsClosestAnswerChoice` models the multiple-choice approximation without
  falsely equating the idealized physical duration `2000/17 ms` with exactly
  `120 ms`.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration was found for an ultrasonic autofocus echo,
  reflected acoustic pulse, or a two-leg round-trip travel-time law.
  `UnitExamples.SpeedEq` is a dimensional near miss: it acts on one `WithDim`
  value at a time and does not represent `Dimensionful` routes or reflection.
- No searched declaration supplies the speed of sound in air from ambient
  conditions. The source omits both air temperature and the intended speed.
  The conventional exercise calibration `340 m/s` yields `2000/17 ms` and
  makes `120 ms` the unique closest choice. An authoritative redraft should
  state the intended sound speed or atmospheric conditions explicitly.
- The assigned `.lean` file and `.archon/AGENTS.md` were absent at task start.
  The complete available role file
  `.archon/prover-modes/physics-formalize.md` was read instead, and there were
  no pre-existing `/- USER: ... -/` hints to preserve.
- The advertised `archon` executable was not available on this runtime's
  `PATH`, so the DAG node and ancestor queries could not be completed. The
  source report independently confirms that this problem has no previous
  parts.

## Verification

- `archon-lean-lsp` diagnostics report success with exactly two expected
  `declaration uses sorry` warnings, one for the exact intermediate lemma and
  one for the final theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0211.lean` exits with code
  0 and reports the same two expected `sorry` warnings, with no errors.
