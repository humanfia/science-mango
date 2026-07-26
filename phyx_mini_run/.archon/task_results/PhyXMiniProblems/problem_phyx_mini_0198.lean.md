# Autoformalization result: `problem_phyx_mini_0198.lean`

## Assumption/target split

### Governing laws

- `SatisfiesMachConeAndFlightLaws.airplane_speed_from_mach` states the general dimensionless Mach relation `v_s = M c` in any compatible length/time units.
- `mach_cone_relation` states the Mach-cone law `sin alpha = c / v_s`.
- `horizontal_distance_is_vs_mul_t` states the steady-flight kinematic relation represented by the figure label `v_s t`.
- `right_triangle_tangent` states `tan alpha = h / (v_s t)` for the listener/airplane right triangle.
- `shock_path_pythagorean` identifies the labeled shock-wave segment as the triangle's hypotenuse.
- `HasPhysicalSonicBoomParameters` supplies positivity, `M > 1`, and the acute-angle branch. It contains no numerical boom-delay value.

### Previous-part results

- None. The source report has no previous parts.

### Figure/data readouts

- `MatchesProblemAndFigure` records the airplane, listener `L`, shock-wave label, rightward flight, and the fact that the initial airplane ground projection is `L` (directly overhead).
- It records `h = 8000 m`, `c = 320 m/s`, and `M = 7/4 = 1.75`.
- `SonicBoomSetup` includes the figure-derived Mach angle `alpha`, horizontal leg from `L` to the current aircraft ground projection, shock-wave slant length, airplane speed `v_s`, and the unknown `boomDelay`.

### Current target conclusions

- `boomDelay_formula` concludes the general derived relation
  `t = h * sqrt (M^2 - 1) / (M c)`.
- `boomDelay_matches_recordedAnswerB` concludes the exact instance value
  `t = 25 * sqrt 33 / 7` seconds and agreement, within half a tenth of a second, with recorded choice B (`20.5 s`).

## Goal-faithfulness audit

The unknown `boomDelay` is an independent dimensionful field. Neither `MatchesProblemAndFigure`, `HasPhysicalSonicBoomParameters`, nor `SatisfiesMachConeAndFlightLaws` gives its numerical value, the exact radical expression, `20.5`, choice B, or `MatchesAnswerChoice`. The premise law `x = v_s t` is a general kinematic relation, while the Mach-cone and triangle laws remain general physical/geometric relations. The exact and rounded answers occur only in lemma/theorem conclusions. No local definition makes either substantive conclusion true by unfolding.

The source wording “how long will you hear the sonic boom?” is disambiguated using the primary figure and the recorded `20.5 s` answer: `boomDelay` is the elapsed time from the overhead passage until the trailing shock reaches `L`, not the microscopic pulse duration.

## Declarations created and blueprint labels

- Dimensionful/readout API: `AcousticLength`, `AcousticDuration`, `lengthReadout`, `durationReadout`, `speedReadout`, `lengthInMeters`, `durationInSeconds`, and `speedInMetersPerSecond`.
- Figure labels/model: `AircraftLabel`, `ListenerLabel`, `WavefrontLabel`, `AxialDirection`, and `SonicBoomSetup`.
- Assumption predicates: `MatchesProblemAndFigure`, `HasPhysicalSonicBoomParameters`, and `SatisfiesMachConeAndFlightLaws`.
- Derived statement: `boomDelay_formula`.
- Answer model: `AnswerChoice`, `AnswerChoice.seconds`, `MatchesAnswerChoice`, and `recordedAnswerChoice`.
- Blueprint target `thm:physics:phyx_mini_0198:target`: `PhyXMiniProblems.ProblemPhyXMini0198.boomDelay_matches_recordedAnswerB`.

The target environment is ready for `\lean{PhyXMiniProblems.ProblemPhyXMini0198.boomDelay_matches_recordedAnswerB}` and `\leanok`. I did not edit the blueprint because the prover write permissions explicitly restrict this lane to the assigned Lean file and task-result file; the project's role instructions also reserve marker synchronization for a later phase.

## LeanExplore queries/candidates actually used

- `Mach number speed of sound sonic boom Mach angle`: no sonic-boom/Mach-cone law was found. It did ground the available angle/speed area and motivated a faithful local governing-law structure.
- `physical dimensional quantity length time velocity SI units`, `Quantity physical dimension SI value`, `Dimensionful SI quantity length time speed`, and `PhysLean units dimensional analysis Quantity`: selected `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`, and `DimSpeed`.
- `real angle sine tangent arctan trigonometric identity tan`, `Real.sin real sine function`, and `Real.tan`: selected scalar-radian `Real.sin` and `Real.tan`. `Real.Angle.tan` was inspected but not used because the physical acute-branch inequalities are naturally stated for a real radian readout.
- `Real.sqrt square root nonnegative real` and `Real.sqrt`: selected `Real.sqrt` for the derived radical expression.
- `abs_lt real absolute value less than`: grounded real absolute-value notation used by the answer-tolerance predicate.
- `WithDim physical dimension tagged real value cast multiplication division`: inspected `WithDim` and its arithmetic/cast support. The final laws use unit-independent quantities with named compatible-unit readouts, so `WithDim.cast` was not needed.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful` and `UnitChoices.SI` (`Physlib.Units.Basic`); `Dimension`, `Dimension.L𝓭`, and `Dimension.T𝓭` (`Physlib.Units.Dimension`); `WithDim` (`Physlib.Units.WithDim.Basic`); `DimSpeed` (`Physlib.Units.WithDim.Speed`).
- Mathlib: `Real.sin` and `Real.tan` (`Mathlib.Analysis.Complex.Trigonometric`), `Real.sqrt` (`Mathlib.Analysis.Real.Sqrt`), real absolute-value notation, and `Set.Ioo`.

## Local abstractions introduced

- The label inductives preserve the explicitly drawn airplane, listener `L`, shock wave, and flight direction.
- `SonicBoomSetup` preserves independent dimensionful physical quantities and gives the figure legs/slant path explicit roles.
- `SatisfiesMachConeAndFlightLaws` is the smallest local interface for the missing Mach-cone, steady-flight, and right-triangle physics; it states general laws rather than the requested answer.
- `MatchesAnswerChoice` models the displayed one-decimal precision with a `0.05 s` half-increment tolerance.

## Grounding gaps

- LeanExplore found no Mathlib/Physlib declaration for sonic booms, Mach number, or the Mach-cone law `sin alpha = c / v_s`; these are represented by the local law interface above.
- The blueprint target currently has no `\lean{...}` declaration hint. A later blueprint-owning phase should add the fully qualified theorem name listed above; no mathematical redraft is otherwise required.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0198.lean` succeeds. The only diagnostics are the expected `sorry` warnings for `boomDelay_formula` and `boomDelay_matches_recordedAnswerB`.
