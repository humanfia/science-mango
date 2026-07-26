# Autoformalization result: `problem_phyx_mini_0336.lean`

## Assumption/target split

### Governing laws

- `SatisfiesLungIdealGasLaws.gaugePressureToAbsolutePressure` states that, at every position on the breath cycle, absolute pressure is ambient pressure plus the gauge pressure plotted in the figure.
- `SatisfiesLungIdealGasLaws.CelsiusToKelvin` states the Celsius-to-kelvin conversion for the air temperature at every cycle position.
- `SatisfiesLungIdealGasLaws.idealGasLaw` states `P V = n R T` at every cycle position in the compatible readouts mmHg, L, mol, and K.
- `MatchesPrimaryLungFigure.volumeIsPiecewiseLinear` and `gaugePressureIsPiecewiseLinear` encode the source's straight-line model on all four directed edges, so “maximum during a breath” is not reduced to a maximum over the vertices alone.

### Previous-part results

- None.  The source report has `previous_parts: []`.

### Figure/data readouts

- The primary bitmap, rather than its conflicting auxiliary caption, gives the four vertices `(0.1 L, 1 mmHg)`, `(0.4 L, 9 mmHg)`, `(1.4 L, 11 mmHg)`, and `(1.0 L, 2 mmHg)`.
- The directed cycle is lower-left → upper-left → upper-right → lower-right → lower-left; the first two outgoing edges are inhalation and the last two are exhalation.
- The axes are `V` in litres and gauge `p` in millimetres of mercury.
- `MatchesProblemData` supplies the ideal-gas model, the standard local ambient-pressure readout `760 mmHg`, constant `20 °C`, and the calibrated molar-gas-constant readout `62.4 L·mmHg/(mol·K)`.
- `HasPhysicalLungParameters` supplies positivity/nonnegativity conditions selecting the physical branch.

### Current target conclusions

- `maximum_amount_of_air_is_answer_B` concludes that the mole amount at the upper-right vertex is at least the mole amount at every position on every straight edge of the cycle.
- It also concludes that this amount is within half a thousandth of `0.059 mol`, hence matches recorded answer B to the displayed precision.

## Goal-faithfulness audit

The maximum assertion and the `0.059 mol` approximation occur only in the conclusion of `maximum_amount_of_air_is_answer_B`.  No setup field stores a maximum, no premise asserts that the upper-right vertex maximizes the mole amount, and no premise fixes any mole amount numerically.  `amountOfAirInMolesAt` is an independent response field throughout the cycle and is constrained only by the ideal-gas law.  The answer-choice function merely transcribes the four displayed choices and does not make the target true by unfolding.

The target ranges over `BreathCyclePosition`, whose edge fraction lies in `[0,1]`, rather than only over the four named vertices.  The piecewise-linear volume and gauge-pressure premises are figure/model readouts; together with constant temperature and the governing ideal-gas law they are sufficient for a later proof to derive, rather than assume, the requested maximum.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0336:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0336.maximum_amount_of_air_is_answer_B`.
- Supporting quantity/readout declarations: `VolumeQuantity`, `PressureQuantity`, `MolarGasConstantQuantity`, `volumeInCubicMeters`, `volumeInLiters`, `pressureInPascals`, `pressureInMillimetersOfMercury`, `temperatureInKelvins`, and `molarGasConstantInLiterMillimetersOfMercuryPerMoleKelvin`.
- Supporting figure/model declarations: `BreathCycleState`, `BreathCyclePosition`, `vertexPosition`, `positionOnEdge`, the axis/unit/phase/model enums, `LungPressureVolumeFigure`, and `LungBreathSetup`.
- Premise interfaces: `MatchesPrimaryLungFigure`, `MatchesProblemData`, `HasPhysicalLungParameters`, and `SatisfiesLungIdealGasLaws`.
- Multiple-choice declarations: `AnswerChoice`, `answerAmountInMoles`, and `recordedAnswerChoice`.

The target theorem is ready for the blueprint statement's `\leanok` marker.  I did not edit the chapter because this prover's explicit write permissions restrict changes to the assigned Lean file and this result file; the project role documentation also reserves blueprint-marker synchronization for later infrastructure/review.

## LeanExplore queries and candidates actually used

All four post-formalization searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `ideal gas law pressure volume amount of substance temperature` found `IdealGas.ideal_gas_law`, `DimPressure`, `Temperature`, and `Temperature.toReal`.
- Likely-name query `DimPressure millimeterOfMercury` found `DimPressure.millimeterOfMercury`, `DimPressure`, `Dimensionful`, and `WithDim`.
- Mixed name/concept query `Temperature toReal Celsius kelvin` found `Temperature.toReal`, `Temperature`, `TemperatureUnit`, and `TemperatureUnit.kelvin`; it exposed no offset-Celsius object.
- Natural-language query `Dimensionful volume litre amount of substance mole` found the generic `Dimensionful` infrastructure but no dedicated litre or amount-of-substance/mole declaration.

Source, module, and docstring were fetched only for candidates actually evaluated for this model: `IdealGas.ideal_gas_law`, `DimPressure`, `DimPressure.millimeterOfMercury`, `Temperature`, `Temperature.toReal`, and `Dimensionful`.  The first is a documented near miss; the other five ground declarations used in the file.

## Physlib/Mathlib names grounded

- `DimPressure` and `DimPressure.millimeterOfMercury` from `Physlib.Units.WithDim.Pressure`.
- `Temperature` and `Temperature.toReal` from `Physlib.Thermodynamics.Temperature.Basic`.
- `Dimensionful`, `WithDim`, `UnitChoices.SI`, and the dimension symbols `L𝓭`, `M𝓭`, `T𝓭`, and `Θ𝓭` from Physlib's units infrastructure.
- `Set.Icc` from Mathlib is used to constrain each straight-edge fraction to the physical segment.

Archon Lean LSP local search independently confirmed `DimPressure` and `Dimensionful`; hover checks in the elaborated file confirmed `Dimensionful`, `DimPressure`, `DimPressure.millimeterOfMercury`, and `Temperature.toReal` with their imported modules.

## Local abstractions introduced

- `VolumeQuantity` is a genuine Physlib `Dimensionful` length-cubed quantity, not a scalar alias.  Litres are a named scalar readout obtained by converting the SI cubic-metre value by `1000`.
- `MolarGasConstantQuantity` carries the energy-per-temperature dimension.  Its inverse-mole role is documented and paired with the explicit mole readout because Physlib's current five-component `Dimension` has no amount-of-substance coordinate.
- `amountOfAirInMolesAt : BreathCyclePosition → ℝ` is explicitly a scalar readout in moles, not a replacement definition for an abstract physical amount and not a field containing the answer.
- `BreathCyclePosition` preserves the continuous, four-segment geometry of the plotted cycle; it prevents the requested maximum from being weakened to a finite-vertex claim.
- `SatisfiesLungIdealGasLaws` is a faithful local law interface because the available library theorem is not compatible with this molar, dimensionful clinical model.

## Grounding gaps and redraft requests

- `IdealGas.ideal_gas_law` is a near miss: its source uses a natural-number particle count and a unitless system with `R = 1`.  It cannot directly express a real-valued mole amount with mmHg/L/K readouts, so it was not applied.
- Physlib has no amount-of-substance dimension/type and no dedicated litre unit in the searched API.  The formalization therefore uses an explicit mole scalar readout and an SI-to-litre conversion while retaining dimensions for the other physical quantities.
- Physlib exposes a temperature scale but no searched offset-Celsius temperature object; the `+ 273.15` conversion is therefore stated as a governing relation.
- The auxiliary caption misreads the primary image's vertices.  The blueprint/source should continue to treat the bitmap as primary evidence; the formalization uses the clearly gridded coordinates listed above.
- The requested `.archon/AGENTS.md` file was absent in this checkout.  I followed the injected prover-role instructions and `.archon/prover-modes/physics-formalize.md`; the archived role document also agrees that provers do not edit blueprint chapters.
- The `archon` executable was not available on `PATH` (`command not found`), so the read-only dependency query could not be run.  The target chapter declares no prior theorem dependencies.

## Source/law/answer audit

- The source report lists no previous parts.  The primary bitmap was inspected after the Lean model existed and confirms the axes, gauge-pressure warning, four coordinates, straight edges, and directed breathing phases encoded by `MatchesPrimaryLungFigure`.
- The auxiliary caption conflicts with that bitmap (for example, it describes the left edge as nearly constant-volume and misreads several coordinates), so it is not used as a numerical premise.
- The governing laws are pressure conversion, Celsius-to-kelvin conversion, and `P V = n R T`; the calibrated ambient pressure and molar gas constant are separate problem/reference data.
- These data give approximately `0.0590076 mol` at the upper-right vertex.  Thus the theorem's strict `0.0005 mol` tolerance supports displayed answer B (`0.059 mol`) without assuming either the maximum location or the answer value.
- The blueprint target environment is ready for `\leanok`, but the explicit write permissions prohibit editing blueprint chapters in this task.  A coordinating agent should add the marker.
- The assigned Lean file contained no `/- USER: ... -/` comment.  The exact iteration-002 review reason was missing post-formalization evidence; this report supplies evidence tied to the actual current Lean model.

## Verification

- Archon Lean LSP diagnostics: success, with only `declaration uses sorry` at the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0336.lean`: exit code 0, with only the expected `sorry` warning.
