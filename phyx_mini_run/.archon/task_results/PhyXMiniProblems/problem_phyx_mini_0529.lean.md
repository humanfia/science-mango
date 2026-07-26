# Autoformalization result: `problem_phyx_mini_0529.lean`

## Assumption/target split

### Governing laws

- `SatisfiesUniformBallMotionInMovingFrame setup` states the symbolic constant-velocity relation `Delta x' = u' * Delta t'` for the ball between the throw and catch events in Owen and Dina's rest frame. It does not assign either frame's elapsed time a displayed value.
- `SatisfiesLorentzTimeTransformation setup` states the longitudinal event-difference law `Delta t = gamma(beta) * (Delta t' + beta * Delta x' / c)` for the transformation from the moving frame `S'` to the ground frame `S`. The sign is fixed by the independently recorded rightward frame velocity and leftward event displacement.
- `EdMeasuresGroundFrameElapsedTime setup` identifies Ed's measured duration with the ground-frame coordinate-time difference because Ed is at rest in `S`.
- `HasPhysicalRelativisticParameters setup` records positivity, subluminal speeds, leftward ball motion, and time ordering. These are physical admissibility conditions, not numerical flight-time conclusions.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesScenarioAndPrimaryFigure setup` records that Dina and Owen are at rest in `S'`, Ed is at rest in `S`, the axes are `x'` and `x`, `S'` moves right, Owen is to Dina's right, and the ball travels left.
- The primary bitmap `phyx_data/test_image/529.png` was inspected directly. Its printed readouts are represented exactly as `3/5` for `0.600 c`, `4/5` for the ball's speed magnitude `0.800 c`, and `(9/5) * 10^12` metres for the rest-frame separation. The signed ball velocity is related to the negative of the printed magnitude.
- The throw event is at Owen's `S'` rest position and the catch event is at Dina's `S'` rest position; their rest-position separation is the independently represented dimensionful length.
- `displayedTimeSeconds` and `recordedDatasetAnswer` transcribe the four printed answer values and the dataset's recorded label D as metadata only.

### Current target conclusions

- `ballFlightTimeInEdFrame_matches_answerD` concludes that Ed's measured ground-frame flight duration lies within the stated three-significant-figure rounding tolerance of `4.88 * 10^3 s`, the time printed for answer D.

## Goal-faithfulness audit

`RelativisticCatchSetup.edMeasuredFlightTime` is an independent dimensionful duration. No setup field defines it as `4880 s`, as a displayed choice, or as the result of the target calculation. The scenario and physical-parameter premises contain only source/figure readouts, event geometry, signs, positivity, speed bounds, and time ordering. The three law premises remain symbolic in the unknown moving- and ground-frame event times.

The answer-list definitions are literal source metadata. `MatchesDisplayedTimeChoice` is a rounding comparison, not a definition of the physical duration, and no premise assumes it. Consequently the numerical time and selection of D occur only in the theorem conclusion. The required route remains substantive: derive the moving-frame interval from separation and ball speed, transform the event interval with the Lorentz law, and identify the result with Ed's measurement.

Lengths, durations, signed positions, clock coordinates, and signed velocities use Physlib's unit-independent `Dimensionful (WithDim ... )` representation. They are not scalar aliases. Real values occur only as named-unit readouts, dimensionless speed ratios, answer-list values, and exact rational transcriptions of printed annotations.

## Declarations created and blueprint correspondence

- Dimensionful quantity/readout layer: `LengthQuantity`, `DurationQuantity`, `AxialCoordinate`, `ClockCoordinate`, `AxialVelocity`, the generic unit readout functions, the SI readout helpers, `vacuumSpeedOfLightReadout`, and `velocityInLightSpeedUnits`.
- Scenario labels: `InertialFrameLabel`, `CoordinateAxisLabel`, `ObserverLabel`, `CatchEvent`, `AxialDirection`, and `FigureFeature`.
- Physical objects: `RelativisticCatchFigure` and `RelativisticCatchSetup`.
- Assumption layer: `MatchesScenarioAndPrimaryFigure`, `HasPhysicalRelativisticParameters`, `SatisfiesUniformBallMotionInMovingFrame`, `SatisfiesLorentzTimeTransformation`, and `EdMeasuresGroundFrameElapsedTime`.
- Answer metadata: `AnswerChoice`, `displayedTimeSeconds`, `recordedDatasetAnswer`, and `MatchesDisplayedTimeChoice`.
- `ballFlightTimeInEdFrame_matches_answerD` corresponds to blueprint label `thm:physics:phyx_mini_0529:target`.

## LeanExplore queries and candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language unit query: `physical dimensionful quantities with units length time velocity speed of light`.
- Natural-language relativity query: `Lorentz gamma factor and time transformation between inertial frames`.
- Likely unit-name query: `Dimensionful WithDim LengthUnit TimeUnit`.
- Likely Lorentz-name query: `LorentzGroup.γ`.
- Quantity-role query: `dimensionful physical length and duration quantities with SI unit readouts`.

Source and module information was fetched for:

- `Dimensionful` (ID 394284), defined in `Physlib.Units.Basic` as the subtype of unit-choice-indexed representations satisfying the required dimensional scaling law;
- `DimSpeed.speedOfLight` (ID 394486), defined in `Physlib.Units.WithDim.Speed` as the dimensionful exact value `299792458 m/s`;
- `LorentzGroup.γ` (ID 391166), defined in `Physlib.Relativity.LorentzGroup.Boosts.Basic` as `1 / sqrt (1 - beta^2)`;
- `Lorentz.Vector.boost_time_eq` (ID 391162), from `Physlib.Relativity.LorentzGroup.Boosts.Apply`, inspected as a near match for the event-time transformation.

The final formalization directly uses `Dimensionful`, `DimSpeed.speedOfLight`, and `LorentzGroup.γ`. `Lorentz.Vector.boost_time_eq` is not used directly: it is expressed for a dimensionless Lorentz vector and the library's `boost beta` convention gives a `gamma * (t - beta*x)` component. The scenario needs the inverse-direction `S'`-to-`S` relation, dimensionful coordinate readouts, and an explicit `c` conversion. The local generic law records exactly that convention without assuming the requested numerical result.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`, `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, `TimeUnit`, `DimSpeed.speedOfLight`, and `LorentzGroup.γ`.
- Mathlib: `NNReal`, `ℝ`, absolute value, powers, ordered-field arithmetic, and the imported real square-root infrastructure used by `LorentzGroup.γ`.

The file now imports `Mathlib` explicitly in addition to the relevant Physlib modules, addressing the retry gate's concern that the target had not been checked in a real Lake/Mathlib environment.

## Local abstractions introduced

- The five physical quantity aliases specialize Physlib's `Dimensionful (WithDim ...)` API to nonnegative length/duration and signed one-dimensional position/time/velocity roles. This preserves dimensions and unit-change behavior while distinguishing physical quantities from scalar readouts.
- The frame, observer, event, axis, direction, and figure-feature enums preserve the named scenario and the primary image's sign-sensitive geometry.
- `RelativisticCatchFigure` is the smallest figure abstraction that retains named features, frame/axis labels, directions, ordering, and the three printed scalar annotations.
- `RelativisticCatchSetup` keeps physical quantities and frame-indexed event coordinates independent; in particular, the requested duration is not defined from answer metadata.
- The three `Satisfies...` structures provide the uniform-motion law, inverse longitudinal Lorentz time law, and operational measurement relation absent as a directly compatible dimensionful Physlib API.

## Grounding gaps and redraft requests

- LeanExplore found Physlib's general Lorentz-vector boost component lemma, but no ready-made theorem combining dimensionful event coordinates, explicit speed-of-light conversion, the inverse boost convention, and observer-measured elapsed duration. The faithful local law interfaces above fill that gap.
- No specialized Physlib aliases for nonnegative physical length and duration appeared in the searches; the local aliases therefore specialize the grounded generic dimensional API rather than collapsing quantities to reals.
- The prompt-listed `.archon/AGENTS.md` is absent. The available `.archon/prover-modes/physics-formalize.md` was read completely and followed as the stage-specific role document.
- The `archon` executable was not available on `PATH`, so the optional dependency-graph query could not run. The source report independently establishes that there are no previous parts.
- The file-specific `/- USER: ... -/` comment says the assigned source file did not exist when autoformalization began; it has been preserved.
- The blueprint chapter exists but was not edited with `\leanok`, because the explicit write permissions restrict this agent to the assigned Lean file and this result report. The marker-sync or plan agent should add `\leanok` to `thm:physics:phyx_mini_0529:target`.

## Verification

- `archon-lean-lsp` diagnostics report exactly one expected `declaration uses sorry` warning and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0529.lean` exits with code 0 and the same expected warning.

---

# Prover result: `PhyXMiniProblems/problem_phyx_mini_0529.lean`

## `ballFlightTimeInEdFrame_matches_answerD` (line 370)

### Attempt 1

- **Approach:** Recovered the exact SI speed of light from
  `DimSpeed.speedOfLight_in_SI`; derived the signed moving-frame displacement,
  frame velocity ratio, ball velocity ratio, and separation from `hScenario`;
  solved the uniform-motion and Lorentz-time equations; then proved both sides
  of the `5 s` rounding interval by exact linear arithmetic.
- **Result:** RESOLVED.
- **Key insight:** After evaluating `LorentzGroup.γ (3 / 5) = 5 / 4`, every
  remaining physical law is a linear equation over exact rational real
  constants, so `linarith` certifies the displayed-answer interval without
  decimal approximation.

## Verification

- `archon-lean-lsp` diagnostics: no errors and no `sorry` warning; only the
  harmless unused-contract-parameter warning for `hPhysical`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0529.lean`: exit code 0.
- `lean_verify`: no suspicious source patterns; theorem axioms are only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Source scan: zero occurrences of `sorry`, `admit`, `axiom`,
  `native_decide`, or `sorryAx`.

## Blueprint marker

The target theorem is proof-complete and eligible for `\leanok`. The blueprint
was not edited because this prover's explicit write permissions are limited to
the assigned Lean file and this task-result file; the marker-sync agent should
mark `thm:physics:phyx_mini_0529:target`.

## Summary

- Sorry count: **1 → 0**.
- Closed:
  `PhyXMiniProblems.ProblemPhyXMini0529.ballFlightTimeInEdFrame_matches_answerD`.
- Still open: none.
- Adjacent sorries beyond the assigned theorem: none existed.
- New helper declarations: none.
- Redraft needed: no.

## Why I stopped

**Real progress:** closed the one assigned sorry with a compiling, axiom-clean
proof. The file is complete, so there is no remaining in-scope proof
obligation. No identified approach was left unattempted.
