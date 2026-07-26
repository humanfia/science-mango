# Autoformalization result: `problem_phyx_mini_0693.lean`

## Review outcome

Iteration 003 audited the completed Lean model against the chapter, the source
report, and the primary raster image.  The formalization is source-faithful and
was preserved.  The review-gate reason was evidence-only: the earlier generic
grounding preflight did not document searches and declarations actually used
by the completed model.  This is the requested post-formalization report.

The chapter contains `% archon:physics`.  The requested `.archon/AGENTS.md`
does not exist, so `.archon/prover-modes/physics-formalize.md` supplied the
project role.  The file-specific `USER` comment says that the assigned Lean
file did not exist when its initial autoformalization began.

## Physical model extracted

- The outfielder, bounce point, and catcher are ordered along horizontal
  ground; the complete separation is the physical length `distanceD`, labelled
  `D` in the image.
- The green direct arc is launched at `45°`.  The two blue arcs use the same
  acute launch angle `θ`, with `0 < θ < 45°` selecting the lower-angle branch.
- The direct arc and the first blue arc use the same comparison launch speed.
  The second blue arc is launched with half the speed immediately before the
  bounce.  Under ideal no-drag equal-height motion, that incoming magnitude is
  the first blue arc's launch speed.
- Each arc has an independent dimensionful range, launch speed, and duration.
  The model also retains dimensionful gravity and the full baseline length.
- Length has dimension `L`, duration `T`, speed `L T⁻¹`, and acceleration
  `L T⁻²`.  Real scalars are used only for coherent SI readouts, diagram
  coordinates, radian/angle operations, and the requested dimensionless ratio.
- Both routes connect the same endpoints: the direct range is `D`, while the
  two blue ranges sum to `D`.
- The displayed choices are A `0.870`, B `0.647`, C `0.949`, and D `0.511`;
  dataset metadata records C.

## Assumption/target split

### Governing laws

- `SatisfiesIdealLevelGroundProjectileLaws` gives the no-drag equal-height
  impact-speed equality for the first blue arc.
- Its `levelGroundRangeLaw` gives
  `R = v² * sin (2 * α) / g` for every arc.
- Its `levelGroundFlightTimeLaw` gives
  `t = 2 * v * sin α / g` for every arc.
- These are general mechanics relations.  They mention neither the requested
  time ratio nor any numerical answer choice.

### Previous-part results

- None.  The source report has `previous_parts: []`; no earlier result is
  assumed.

### Figure/data readouts and scenario facts

- `MatchesPrimaryBaseballFigure` records the left-to-right spatial order,
  horizontal ground, blue and green trajectory colors, dashed arcs, three
  launch arrows, the two `θ` labels, the `45°` label, and the baseline `D`.
- `MatchesBaseballThrowScenario` records exactly one bounce, equal endpoint
  heights, the direct `π/4` angle, equal blue angles, the lower-angle branch,
  equal initial comparison speeds, the half-incoming-speed rebound, and the
  two endpoint range constraints.
- `HasPhysicalBaseballThrowParameters` supplies only positivity and
  nondegeneracy of the distance, gravity, speeds, ranges, and durations.

### Current target conclusions

- `bounceLaunchAngleSine_exact` derives
  `sin θ = 1 / Real.sqrt 5`.
- `oneBounceToNoBounceTimeRatio_exact` derives the requested exact ratio
  `3 / Real.sqrt 10`.
- `problem_phyx_mini_0693` concludes that exact ratio, agreement with the
  three-decimal display `0.949`, and unique closest-choice status for C.

## Source/law/answer audit

The source report and image support the named objects, the equal-angle bounce,
the direct `45°` arc, the common endpoint distance, and the four choices.  The
same-initial-speed comparison is implicit in the two same-origin launch arrows
and is necessary for the recorded numerical answer; it is exposed as a
scenario field rather than hidden in a definition.  Equal-height impact-speed,
range, and time equations are classified separately as governing laws.  The
recorded answer is metadata only: neither C nor `0.949` occurs in a premise.

## Goal-faithfulness audit

The requested ratio does not occur in `BaseballOneBounceSetup`,
`MatchesPrimaryBaseballFigure`, `MatchesBaseballThrowScenario`,
`HasPhysicalBaseballThrowParameters`, or
`SatisfiesIdealLevelGroundProjectileLaws`.  The setup stores independent
dimensionful ranges, speeds, durations, distance, and gravity.
`oneBounceToNoBounceTimeRatio` merely divides the sum of the independently
stored blue-leg durations by the independently stored direct duration; it does
not define the answer.  The exact angle relation, exact ratio, rounding claim,
and unique-choice claim occur only as conclusions with `by sorry` bodies.

The primitive quantities are not scalar aliases or one-field scalar wrappers:
length, duration, and acceleration use `Dimensionful (WithDim ... NNReal)`,
and speed uses Physlib's dimensionful `DimSpeed`.

## Declarations and blueprint labels

For compactness, `D` below abbreviates the exact label prefix
`def:physics:phyx-mini-0693:phyxminiproblems-problemphyxmini0693-` and `L`
abbreviates `lem:physics:phyx-mini-0693:phyxminiproblems-problemphyxmini0693-`.

| Lean declaration | Blueprint label |
| --- | --- |
| `accelerationDimension` | `Daccelerationdimension` |
| `LengthQuantity` | `Dlengthquantity` |
| `DurationQuantity` | `Ddurationquantity` |
| `AccelerationQuantity` | `Daccelerationquantity` |
| `nonnegativeSIReadout` | `Dnonnegativesireadout` |
| `lengthInMeters` | `Dlengthinmeters` |
| `durationInSeconds` | `Ddurationinseconds` |
| `speedInMetersPerSecond` | `Dspeedinmeterspersecond` |
| `accelerationInMetersPerSecondSquared` | `Daccelerationinmeterspersecondsquared` |
| `ThrowSegment` | `Dthrowsegment` |
| `GroundPoint` | `Dgroundpoint` |
| `TrajectoryColor` | `Dtrajectorycolor` |
| `FigureAngleLabel` | `Dfigureanglelabel` |
| `BaseballThrowFigure` | `Dbaseballthrowfigure` |
| `BaseballOneBounceSetup` | `Dbaseballonebouncesetup` |
| `MatchesPrimaryBaseballFigure` | `Dmatchesprimarybaseballfigure` |
| `MatchesBaseballThrowScenario` | `Dmatchesbaseballthrowscenario` |
| `HasPhysicalBaseballThrowParameters` | `Dhasphysicalbaseballthrowparameters` |
| `SatisfiesIdealLevelGroundProjectileLaws` | `Dsatisfiesideallevelgroundprojectilelaws` |
| `oneBounceFlightTimeInSeconds` | `Donebounceflighttimeinseconds` |
| `noBounceFlightTimeInSeconds` | `Dnobounceflighttimeinseconds` |
| `oneBounceToNoBounceTimeRatio` | `Donebouncetonobouncetimeratio` |
| `AnswerChoice` | `Danswerchoice` |
| `AnswerChoice.displayedRatio` | `Danswerchoice-displayedratio` |
| `recordedDatasetAnswer` | `Drecordeddatasetanswer` |
| `MatchesDisplayedThreeDecimalRatio` | `Dmatchesdisplayedthreedecimalratio` |
| `IsUniqueClosestDisplayedRatio` | `Disuniqueclosestdisplayedratio` |
| `bounceLaunchAngleSine_exact` | `Lbouncelaunchanglesine-exact` |
| `oneBounceToNoBounceTimeRatio_exact` | `Lonebouncetonobouncetimeratio-exact` |
| `problem_phyx_mini_0693` | `thm:physics:phyx_mini_0693:target` |

All Lean names are in namespace
`PhyXMiniProblems.ProblemPhyXMini0693`.

## LeanExplore queries and candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `ideal projectile motion horizontal range flight time
  equal launch landing height uniform gravity` returned unrelated
  `Ideal.*` algebra declarations and generic `Time`, but no projectile API.
- Natural-language query `projectile returning to launch height landing speed
  equals launch speed no drag` returned `DimSpeed`, `UnitExamples.SpeedEq`,
  constant-speed curve declarations, and harmonic-oscillator near misses, but
  no equal-height projectile theorem.
- Natural-language query `dimensionful physical quantity SI units length time
  speed acceleration` returned `UnitChoices.SI`, `Dimension`,
  `Dimensionful`, and `DimSpeed`.
- Likely-name query `DimSpeed Dimensionful UnitChoices.SI` confirmed those
  exact Physlib declarations.
- Likely-name query `WithDim Dimension L𝓭 T𝓭` found `Dimension`,
  `Dimension.L𝓭`, and `WithDim.cast`, grounding the tagged-dimension model.
- Likely-name queries `Real.Angle.sin Real.Angle.toReal` and
  `Real.Angle.sin` found `Real.Angle.sin`, `Real.Angle.sin_toReal`, and
  `Real.Angle.sin_two_nsmul`.
- Likely-name query `Real.sqrt` found `Real.sqrt` and its standard algebraic
  lemmas.

Source, module, and docstring fetches were made for the candidates actually
used: `Dimension`, `Dimensionful`, `UnitChoices.SI`, `DimSpeed`,
`Real.Angle.sin`, and `Real.sqrt`.  The returned source confirms that
`DimSpeed = Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`; LeanExplore's short
description calling it “Dimensionless Speed” is inaccurate, while its source
and docstring correctly say it is a speed without a chosen unit.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `UnitChoices.SI`, and `DimSpeed`.
- Mathlib: `NNReal`, `Real.Angle`, `Real.Angle.sin`, `Real.Angle.toReal`,
  `Real.pi`, and `Real.sqrt`.
- Modules fetched: `Physlib.Units.Dimension`, `Physlib.Units.Basic`,
  `Physlib.Units.WithDim.Speed`,
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`, and
  `Mathlib.Analysis.Real.Sqrt`.

## Local abstractions introduced

- `AccelerationQuantity` uses the Physlib dimension machinery with local
  dimension `L T⁻²`; no searched reusable dimensional acceleration alias was
  exposed.
- `BaseballOneBounceSetup` retains each physical role as an independent
  dimensionful quantity, including the impact speed immediately before the
  bounce.
- `SatisfiesIdealLevelGroundProjectileLaws` is the smallest faithful local law
  interface because no searched Mathlib/Physlib declaration packages the
  equal-height impact-speed, range, and time equations.  It does not contain
  the requested answer.
- The figure enums and `BaseballThrowFigure` preserve object identities,
  colors, arrows, angle labels, spatial order, horizontal ground, and `D`
  without treating drawing coordinates as measured distances.
- The answer-choice predicates keep dataset/display metadata separate from
  both physical premises and the exact derived ratio.

## Grounding gaps and redraft requests

- No compatible library theorem for level-ground projectile range, flight
  time, or equal-height impact speed was found; the local governing-law
  interface remains necessary.
- The blueprint provides source text and declaration descriptions but no
  detailed algebraic informal proof.  It could explicitly state the
  same-initial-speed comparison that is currently inferred from the figure and
  recorded answer.
- The task's explicit write permissions forbid editing the blueprint chapter.
  Therefore its environments could not be marked `\leanok`; the plan agent or
  orchestrator should add those markers for the declarations above.

## Verification

- `archon-lean-lsp` reported exactly three expected `declaration uses sorry`
  warnings and no errors or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0693.lean` exited 0 with
  the same three expected warnings at the two derived lemmas and final theorem.

# Prover result: `problem_phyx_mini_0693.lean`

## Status

Complete. All three proof placeholders were replaced without changing any
declaration signature:

- `bounceLaunchAngleSine_exact`
- `oneBounceToNoBounceTimeRatio_exact`
- `problem_phyx_mini_0693`

## Proof summary

- The range laws, common initial comparison speed, equal-height impact-speed
  law, and half-speed rebound reduce the common-endpoint range equation to
  `sin (2 • θ) = 4 / 5`.
- The hypothesis `0 < θ.toReal < π / 4` gives positive sine and cosine with
  `sin θ < cos θ`. Together with the double-angle and unit-circle identities,
  this selects the acute root `sin θ = 1 / sqrt 5`.
- Substitution into the three flight-time laws gives the exact one-bounce to
  no-bounce ratio `3 / sqrt 10`.
- Certified square-root arithmetic proves
  `1897 / 2000 < 3 / sqrt 10 < 949 / 1000`. This establishes the displayed
  three-decimal value `0.949` and, by case analysis, proves choice C strictly
  closer than A, B, or D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0693.lean`: passed with no
  diagnostics.
- Direct same-source `#print axioms` checks for all three completed
  declarations produced no axiom dependencies.
- Source scan found no `sorry`, `admit`, `sorryAx`, introduced `axiom`, or
  `native_decide`.

## Blueprint note

The blueprint chapter exists and was read before editing Lean. Its proved
environments are ready for `\leanok` synchronization, but the chapter was not
edited because this prover assignment explicitly permits writes only to the
assigned Lean file and this task-result file.

## Environment note

The requested run-local `.archon/AGENTS.md` and advertised `archon`
executable were absent. The active `.archon/prover-modes/physics.md`
instructions and `.archon/PROGRESS.md` were used instead.

## Redraft needed

None.
