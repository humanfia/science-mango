# Autoformalization result: `problem_phyx_mini_0941.lean`

## Assumption/target split

### Governing laws

- `SatisfiesIdealSeriesRLTransientLaws.steadyStateOhmsLaw` states the steady-state relation between source emf, designed operating current, and device resistance.
- `SatisfiesIdealSeriesRLTransientLaws.timeConstantLaw` states the physical series R-L law `L = R τ` using henry, ohm, and second readouts.
- `SatisfiesIdealSeriesRLTransientLaws.currentStepResponse` states the ideal energizing transient
  `I(t) = I∞ (1 - exp (-t/τ))`; the exponential argument is a ratio of two time readouts and hence dimensionless.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts

- Prose data: negligible source internal resistance, `R = 175 Ω`, designed current `36 mA`, current ceiling `4.9 mA` throughout the first `58 μs`.
- Primary raster `phyx_data/test_image/941.png`: nodes `a`, `b`, `c`; resistor `R` from `a` to `b`; inductor `L` from `b` to `c`; rightward arrow `i`; source label and positive terminal; open switches `S₁` and `S₂`; magenta resistor; green inductor; and both energizing/discharge captions.
- Source-answer metadata: labels A/B/C/D with payloads 220/390/750/280, all printed in `μH`, and recorded label B. These values and units are not compared with the physical time constant.

### Current target conclusion

- `limitingTimeConstantInMicroseconds ≤ timeInMicroseconds setup.timeConstant`, where the left side is the logarithmic threshold obtained by solving the boundary case of the source's early-current inequality.
- No exact value of the actual time constant, saturation equality, `396–397 μs` interval, or closest-answer assertion is a target.

## Goal-faithfulness audit

The source says that current may rise to *no more than* `4.9 mA` in the first `58 μs`; it does not say the ceiling is attained at the deadline. Accordingly, `MatchesDeviceSafetySpecification` contains only the interval inequality. The former `UsesLimitingSafeDesign` equality was removed, and neither `ProtectiveSeriesRLCircuit` nor any laws structure defines `timeConstant` from the requested logarithmic bound.

The threshold definition is an independent real-valued expression built from source readouts. The theorem must still derive that this expression is a lower bound on the independently stored physical `TimeMagnitude`. Thus the target does not hold by unfolding a field or premise.

The answer choices are dimensionally incompatible with the question: they carry microhenries while `τ` is a time. `displayedChoiceNumber`, `displayedChoiceUnit`, and `recordedDatasetAnswer` retain that contradiction only as source metadata. Cross-dimensional `numericalPayloadDistance` and `IsUniqueClosestNumericalPayload` declarations were removed.

## Declarations and blueprint labels

Retained/formalized declarations correspond to these chapter labels:

- Dimension model: `energyDimension`, `electricCurrentDimension`, `electricPotentialDimension`, `electricalResistanceDimension`, and `inductanceDimension` correspond respectively to labels ending `-energydimension`, `-electriccurrentdimension`, `-electricpotentialdimension`, `-electricalresistancedimension`, and `-inductancedimension` under the common prefix `def:physics:phyx-mini-0941:phyxminiproblems-problemphyxmini0941`.
- Dimensionful quantity types: `VoltageMagnitude`, `ResistanceMagnitude`, `InductanceMagnitude`, `CurrentMagnitude`, and `TimeMagnitude` correspond to labels ending `-voltagemagnitude`, `-resistancemagnitude`, `-inductancemagnitude`, `-currentmagnitude`, and `-timemagnitude`.
- Readouts: `coherentSIReadout`, `voltageInVolts`, `resistanceInOhms`, `inductanceInHenries`, `currentInAmperes`, `currentInMilliamperes`, `timeReadout`, `timeInSeconds`, and `timeInMicroseconds` correspond to labels ending `-coherentsireadout`, `-voltageinvolts`, `-resistanceinohms`, `-inductanceinhenries`, `-currentinamperes`, `-currentinmilliamperes`, `-timereadout`, `-timeinseconds`, and `-timeinmicroseconds`.
- Figure vocabulary: `CircuitNode`, `SwitchLabel`, `CircuitComponent`, `ComponentColor`, `SwitchState`, `BranchCurrentDirection`, `SeriesRLConfiguration`, and `SeriesRLFigure` correspond to labels ending `-circuitnode`, `-switchlabel`, `-circuitcomponent`, `-componentcolor`, `-switchstate`, `-branchcurrentdirection`, `-seriesrlconfiguration`, and `-seriesrlfigure`.
- Physical setup and predicates: `ProtectiveSeriesRLCircuit`, `MatchesSuppliedSeriesRLFigure`, `MatchesSeriesRLSwitchingProtocol`, `MatchesDeviceSafetySpecification`, `HasPhysicalSeriesRLParameters`, and `SatisfiesIdealSeriesRLTransientLaws` correspond to labels ending `-protectiveseriesrlcircuit`, `-matchessuppliedseriesrlfigure`, `-matchesseriesrlswitchingprotocol`, `-matchesdevicesafetyspecification`, `-hasphysicalseriesrlparameters`, and `-satisfiesidealseriesrltransientlaws`.
- Threshold and source metadata: `limitingTimeConstantInMicroseconds`, `AnswerChoice`, `displayedChoiceNumber`, `PrintedAnswerUnit`, `displayedChoiceUnit`, and `recordedDatasetAnswer` correspond to labels ending `-limitingtimeconstantinmicroseconds`, `-answerchoice`, `-displayedchoicenumber`, `-printedanswerunit`, `-displayedchoiceunit`, and `-recordeddatasetanswer`.
- `safeDesign_timeConstant_at_least_limitingValue` corresponds to `lem:physics:phyx-mini-0941:phyxminiproblems-problemphyxmini0941-safedesign-timeconstant-at-least-limitingvalue`.
- `problem_phyx_mini_0941` corresponds to `thm:physics:phyx_mini_0941:target`; its public name was preserved while its statement was repaired to the source-supported lower bound required by the review gate.

Removed as unsupported or cross-dimensional:

- `UsesLimitingSafeDesign` and label ending `-useslimitingsafedesign`.
- `numericalPayloadDistance` and `IsUniqueClosestNumericalPayload`, with labels ending `-numericalpayloaddistance` and `-isuniqueclosestnumericalpayload`.
- `timeConstant_eq_logarithmic_formula` and `limitingTimeConstant_between_396_and_397`, with their corresponding lemma labels.

## LeanExplore grounding

All searches used package filters `packages: ["Mathlib", "Physlib"]`.

Queries actually run:

- `dimensionful physical quantities with units SI readout`
- `Dimensionful WithDim`
- `time unit seconds microseconds TimeUnit`
- `series RL circuit exponential current time constant`
- `electrical resistance inductance voltage current physical quantity`
- `Real.log`
- `RL circuit time constant inductance resistance`

Candidates used and inspected by source/module/docstring:

- `Dimension` (`Physlib.Units.Dimension`): the five foundational physical-dimension exponents.
- `Dimensionful` (`Physlib.Units.Basic`): unit-choice-indexed quantities satisfying a dimension law.
- `UnitChoices.SI` (`Physlib.Units.Basic`): coherent SI choices.
- `TimeUnit.microseconds` (`Physlib.SpaceAndTime.Time.TimeUnit`): `10⁻⁶` seconds.
- `Real.exp` (`Mathlib.Analysis.Complex.Exponential`): the exponential used in the transient law.
- `Real.log` (`Mathlib.Analysis.SpecialFunctions.Log.Basic`): the logarithm used in the threshold expression.

## PhysLean/Mathlib names grounded

- Physlib: `Dimension`, `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.C𝓭`, `Dimensionful`, `WithDim`, `UnitChoices`, `UnitChoices.SI`, `TimeUnit`, `TimeUnit.seconds`, and `TimeUnit.microseconds`.
- Mathlib: `NNReal`, `Real.exp`, and `Real.log`.

## Local abstractions

- The dimension-specific magnitude aliases specialize Physlib's `Dimensionful (WithDim d NNReal)` rather than collapsing voltage, resistance, inductance, current, or time to transparent scalar aliases. Real values occur only at named readout boundaries.
- `SeriesRLFigure` and its finite label/color/direction types preserve the literal raster evidence.
- `ProtectiveSeriesRLCircuit` keeps the physical inductor and time constant as independent fields, and indexes transient current by a physical `TimeMagnitude`.
- The three setup predicates separate image evidence, switch operation, and numerical safety data. `SatisfiesIdealSeriesRLTransientLaws` is a local law interface because the searches found no library series R-L transient API.

## Grounding gaps

- LeanExplore returned no Mathlib/Physlib model for electrical resistance magnitude, inductance magnitude, a switched series R-L circuit, the R-L time-constant law, or its exponential current response. The local dimensionful types and law predicate fill those gaps without assuming the target.
- The `archon` executable advertised for dependency navigation was not available on `PATH`, so no DAG result was used. The target has no external blueprint ancestors indicated in the chapter.
- `.archon/AGENTS.md` was absent in this project checkout. The available `.archon/prover-modes/physics-formalize.md` and the user-supplied role instructions were followed.

## Redraft requests

- The blueprint chapter still describes the rejected saturation assumption, exact numeric interval, closest-payload relation, and removed declarations. It should be regenerated to match the repaired source-supported theorem and dependency list.
- The chapter was not edited or marked `\leanok` because this task's explicit write permissions allow edits only to the assigned Lean file and this result file.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0941.lean` succeeds.
- Lean LSP diagnostics report only the two expected `declaration uses sorry` warnings, for `safeDesign_timeConstant_at_least_limitingValue` and `problem_phyx_mini_0941`.
