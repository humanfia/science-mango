# Autoformalization result: `problem_phyx_mini_0594.lean`

## Assumption/target split

### Governing laws

- `SatisfiesApparentMotionLaws.constantSpeedPathKinematics`: the path distance between the two emission events is the true knot speed times the burst-frame emission interval.
- `SatisfiesApparentMotionLaws.transverseProjectionGivesApparentDistance`: the across-view distance is the sine projection of the path displacement.
- `SatisfiesApparentMotionLaws.earthwardProjectionOfDisplacement`: the second burst is closer to Earth by the cosine projection of the path displacement.
- `SatisfiesApparentMotionLaws.lightTravelArrivalInterval`: because of that earthward advance, the light-arrival interval is the emission interval minus the saved light-travel time at Physlib's vacuum light speed.
- `SatisfiesApparentMotionLaws.apparentSpeedIsDistanceOverArrivalTime`: the problem's stated definition `V_app = D_app / T_app`.
- `HasPhysicalJetObservationParameters` selects positive distances and intervals, an acute approaching direction, and a positive true speed below `c`.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesProblemReadouts` contains only the stated `v = 0.980 c` and `theta = 30 degrees` readouts.
- `MatchesJetScenario` identifies the source as a galaxy, the moving object as an ionized-gas knot, the motion model as constant velocity along the jet path, and both light bursts as emitted and eventually detected on Earth.
- `MatchesSuppliedJetFigure` records the primary raster's two bursts on one path, the velocity arrow from Burst 1 toward Burst 2, two parallel earthward light rays, `theta` between the path and earthward direction, and `D_app` across the observer's view between the rays.
- The figure transcription also retains all literal labels: path of knot of ionized gas, Burst 1, Burst 2, `v`, `theta`, `D_app`, and light rays headed to Earth.

### Current target conclusions

- The dimensionless apparent-speed ratio satisfies
  `beta_app = beta * sin(theta) / (1 - beta * cos(theta))`.
- For `beta = 0.980` and `theta = 30 degrees`, the apparent speed matches choice C, `3.24 c`, to the nearest hundredth of `c`.

## Goal-faithfulness audit

The exact apparent-speed formula and the assertion that the result matches choice C occur only in the conclusion of `apparent_speed_of_ionized_gas_knot_matches_answer_C`. They are absent from `MatchesJetScenario`, `MatchesProblemReadouts`, `MatchesSuppliedJetFigure`, `HasPhysicalJetObservationParameters`, and `SatisfiesApparentMotionLaws`.

The governing-law structure contains only independent kinematics, geometric projections, light propagation, and the problem's explicit definition `V_app = D_app / T_app`. It does not contain the algebraically combined apparent-speed formula or a numerical apparent-speed value. `AnswerChoice.speedOfLightMultiple` faithfully transcribes all four displayed choices, and `MatchesAnswerToNearestHundredth` defines the displayed rounding criterion; neither is a premise. `recordedDatasetAnswer` records the supplied dataset answer but is not used as a hypothesis or as a definitional proof of the theorem.

The physical quantities are not transparent real aliases: lengths and durations use Physlib `Dimensionful (WithDim ... NNReal)`, and speeds use Physlib `DimSpeed`. Real values occur only in named SI readouts, dimensionless ratios, angles, and displayed choice values.

## Declarations created and blueprint labels

- Physical quantity/readout declarations: `LengthQuantity`, `DurationQuantity`, `SpeedQuantity`, `lengthInMeters`, `durationInSeconds`, `speedInMetersPerSecond`, `vacuumSpeedOfLightInMetersPerSecond`, `speedFractionOfLight`, and `angleFromDegrees`.
- Physical and figure vocabulary: `BurstLabel`, `AstrophysicalSource`, `MovingObject`, `KnotMotionModel`, `FigureTextLabel`, `FigureArrow`, `FigureDirection`, and `SuperluminalJetFigure`.
- Model and premise split: `ApparentJetMotionSetup`, `MatchesJetScenario`, `MatchesProblemReadouts`, `MatchesSuppliedJetFigure`, `HasPhysicalJetObservationParameters`, and `SatisfiesApparentMotionLaws`.
- Answer vocabulary: `AnswerChoice`, `AnswerChoice.speedOfLightMultiple`, `MatchesAnswerToNearestHundredth`, and `recordedDatasetAnswer`.
- `apparent_speed_of_ionized_gas_knot_matches_answer_C` corresponds to blueprint label `thm:physics:phyx_mini_0594:target`.

## LeanExplore queries/candidates actually used

- Query `dimensionful physical quantities length time speed velocity with units` found `Dimensionful`, `DimSpeed`, `DimSpeed.speedOfLight`, `Dimension`, and `UnitExamples.SpeedEq`.
- Query `Dimensionful WithDim speed velocity Time length` confirmed `DimSpeed`, `Dimensionful`, `Dimension.L𝓭`, and the speed dimension used by `UnitExamples.SpeedEq`.
- Queries `dimensionful length type WithDim L dimension physical length` and `dimensionful time type WithDim T dimension physical duration` confirmed `WithDim`, `Dimension.L𝓭`, and `Dimension.T𝓭`.
- Query `angle in radians sine Real.Angle` found `Real.Angle.sin` and its angle module.
- Query `degrees to Real.Angle thirty degrees pi divided by six` found representative/conversion lemmas but no dedicated degree constructor suitable for the model.
- Query `special relativity apparent transverse velocity superluminal motion` found general/nearby APIs including `Lorentz.Velocity`, `LorentzGroup.boost`, and rigid-body velocity declarations, but no declaration for the apparent transverse-speed/light-arrival geometry in this problem.
- Query `speed division by speed dimensionless ratio Dimensionful` confirmed the speed-of-light and dimensionful-unit infrastructure. `WithDim.val_div_val` was a near candidate but was not needed because the formalization uses named coherent-SI readouts.
- Source and module information was fetched for `Dimensionful`, `UnitExamples.SpeedEq`, `DimSpeed`, `DimSpeed.speedOfLight`, and `Real.Angle.sin` before using the corresponding APIs.

## PhysLean/Mathlib names grounded

- Physlib `Dimensionful` from `Physlib.Units.Basic`.
- Physlib `WithDim`, `Dimension.L𝓭`, and `Dimension.T𝓭`; the inspected `UnitExamples.SpeedEq` source confirmed speed dimension `L𝓭 * T𝓭⁻¹`.
- Physlib `DimSpeed` and `DimSpeed.speedOfLight` from `Physlib.Units.WithDim.Speed`.
- Physlib `UnitChoices.SI` for coherent metre, second, and metre-per-second readouts.
- Mathlib `Real.Angle`, `Real.Angle.sin`, and `Real.Angle.cos` from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`.

## Local abstractions introduced

- `SuperluminalJetFigure` is a semantic figure transcription because no library type represents the exact labelled raster. It preserves burst labels, arrows, path membership, viewing direction, and the across-view role of `D_app` without introducing target numerics.
- `ApparentJetMotionSetup` keeps the true speed, burst-frame interval, path displacement, earthward projection, transverse apparent distance, arrival interval, and apparent speed as independent dimensionful observables.
- `SatisfiesApparentMotionLaws` supplies the missing domain-specific apparent-motion/light-arrival interface as primitive governing relations. It is intentionally factored before algebraic elimination, so it does not assume the requested combined formula.
- `angleFromDegrees` is a naming conversion to `Real.Angle`; no suitable dedicated degree-valued API surfaced in LeanExplore.
- `MatchesAnswerToNearestHundredth` models the precision of the displayed answers as a dimensionless tolerance of `0.005 c`.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration was found for apparent superluminal jet motion or the formula `beta_app = beta sin(theta) / (1 - beta cos(theta))`; the local governing-law interface is therefore necessary.
- The pre-existing automated grounding log queried only the blueprint's meta phrase `Physics formalization target` and returned unrelated candidates (`Path.target`, `semiformal_result`, and `stereographic_target`). Fresh domain-specific LeanExplore searches were required.
- The requested `.archon/AGENTS.md` role file is absent. The available `.archon/prover-modes/physics-formalize.md` was read and followed as the applicable role specification.
- The assigned Lean file did not exist, so there were no pre-existing `/- USER: ... -/` hints to apply; this fact is recorded in a new USER comment.
- The `archon` executable was not available on `PATH` (`archon: command not found`), so the read-only DAG query could not be used.
- The blueprint environment still needs `\leanok`. It was not edited because this task's explicit write permissions allow changes only to the assigned Lean file and this task-result file; the plan agent or deterministic marker sync should add it after accepting the formalization.

## Verification

- `archon-lean-lsp` diagnostics: one warning, `declaration uses sorry`, on the target theorem; no errors or other warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0594.lean`: exit code 0 with the same single expected `sorry` warning.
- `git diff --check -- PhyXMiniProblems/problem_phyx_mini_0594.lean`: clean.
