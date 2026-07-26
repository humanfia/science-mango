# Autoformalization result: `problem_phyx_mini_0440.lean`

## Iteration 003 review disposition

The exact review-gate reason is evidence-only: the gate could not establish a
genuine post-formalization report for the revised Lean model. I re-audited the
model against the blueprint, source report, primary raster, and current
`physics-formalize` rules, and performed fresh LeanExplore and Lean checks in
this iteration. No semantic redraft of
`PhyXMiniProblems.ProblemPhyXMini0440.problem_phyx_mini_0440` was warranted.

The project-local `.archon/AGENTS.md` requested by the invocation is absent.
I therefore followed the injected prover instructions, the local
`.archon/prover-modes/physics-formalize.md`, and the archived role document
at `../phyx_mini_archives/20260722-review3-rerun/.archon/AGENTS.md`. These
agree that a prover may write only its assigned Lean file and report and must
not edit blueprint chapters.

## Assumption/target split

### Governing laws

- Boiling equilibrium:
  `setup.steamPressureAtBoiling =
  setup.saturationPressureAt setup.boilingTemperature`.
- Incipient-lift vertical force balance:
  `p_steam A = p_atm A + m g`, represented with the named SI readouts
  `pressureForceInNewtons` and `weightInNewtons`.
- Both are fields of `SatisfiesBoilingAndPetcockBalanceLaws`. Neither field
  solves for the mass or mentions an answer choice.

### Previous-part results

- None. The source report's `previous_parts` array is empty.
- The advertised `archon dag-query` navigation could not be used because
  `archon` is not installed on `PATH` in this runtime (exit code 127).

### Figure/data readouts and calibrations

- Scenario readouts: water is the working fluid, the lid is screwed tight,
  the petcock covers the opening, and the petcock is at incipient lift.
- Primary-raster readouts: the supplied image shows a domed closed cooker,
  a lid-mounted petcock, lower `Liquid`, upper `Steam or vapor`, and
  escaping `Steam` above the lid. The raster contains no numerical mass,
  pressure, area, or temperature value.
- Prose data: opening area `5 mm²`, boiling temperature `120 °C`, and
  outside pressure `101.3 kPa`.
- Environmental calibration: `g = 9.8 m/s²`.
- Thermodynamic calibration: saturated-water pressure at the specified
  operating temperature is `198.5 kPa`. This is pressure-valued and is kept
  separate from the displayed answer choice whose numeral is also `198.5`.
- Display metadata: A = `10 g`, B = `198.5 g`, C = `100 g`, and
  D = `50 g`. The table records candidates but does not select one.

### Current target conclusions

- `massInKilograms setup.petcockMass = 243 / 4900`.
- `massInGrams setup.petcockMass = 2430 / 49`, approximately `49.59 g`.
- D is a nearest displayed mass.
- Any nearest displayed mass choice is D, so D is uniquely nearest.

## Goal-faithfulness audit

`PressureCookerSetup.petcockMass` is an independent dimensionful field. No
scenario, image, numerical-readout, gravity, steam-table, or governing-law
premise assigns it a numerical value. In particular:

- `UsesWaterSaturationTableAt120C` constrains a `DimPressure` readout, not
  a mass readout.
- `SatisfiesBoilingAndPetcockBalanceLaws` states equilibrium and force
  balance without rearranging them into the requested mass formula.
- `displayedMassInGrams` records all four source candidates.
- `IsNearestDisplayedMass` compares the independent petcock-mass readout to
  every displayed value; it does not define D to be correct.
- The exact kilogram and gram values, selection of D, and uniqueness of D
  occur only in the theorem conclusion.

Thus the current answer is neither a premise field nor a local definition
that makes the theorem true by unfolding.

## Source/law/answer audit

- Source-supported apparatus and numeric inputs are isolated in
  `MatchesPressureCookerScenario`,
  `MatchesSuppliedPressureCookerFigure`, and `MatchesProblemReadouts`.
- Independent physical calibrations are isolated in
  `UsesStandardNearEarthGravity` and
  `UsesWaterSaturationTableAt120C`.
- Governing physics is isolated in
  `SatisfiesBoilingAndPetcockBalanceLaws`.
- Recorded answer metadata is isolated in `displayedMassInGrams`.
- Derived numeric mass and answer selection remain in
  `problem_phyx_mini_0440`.

The arithmetic encoded by the conclusion is dimensionally consistent:
`(198.5 - 101.3) kPa · 5 mm² / (9.8 m/s²) =
243/4900 kg = 2430/49 g`, which is uniquely closest to `50 g`.

## Declarations and blueprint correspondence

All names below are in namespace
`PhyXMiniProblems.ProblemPhyXMini0440`.

| Declaration | Blueprint label |
|---|---|
| `MassQuantity` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-massquantity` |
| `AccelerationQuantity` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-accelerationquantity` |
| `MeasuredTemperature` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-measuredtemperature` |
| `areaReadout` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-areareadout` |
| `areaInSquareMeters` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-areainsquaremeters` |
| `areaInSquareMillimeters` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-areainsquaremillimeters` |
| `massReadout` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-massreadout` |
| `massInKilograms` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-massinkilograms` |
| `massInGrams` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-massingrams` |
| `accelerationInMetersPerSecondSquared` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-accelerationinmeterspersecondsquared` |
| `pressureInPascals` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-pressureinpascals` |
| `pressureInKilopascals` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-pressureinkilopascals` |
| `temperatureInKelvin` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-temperatureinkelvin` |
| `temperatureInDegreesCelsius` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-temperatureindegreescelsius` |
| `pressureForceInNewtons` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-pressureforceinnewtons` |
| `weightInNewtons` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-weightinnewtons` |
| `WorkingFluid` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-workingfluid` |
| `PetcockState` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-petcockstate` |
| `FigureLabel` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-figurelabel` |
| `FigureRegion` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-figureregion` |
| `PressureCookerFigure` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-pressurecookerfigure` |
| `PressureCookerSetup` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-pressurecookersetup` |
| `MatchesPressureCookerScenario` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-matchespressurecookerscenario` |
| `MatchesSuppliedPressureCookerFigure` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-matchessuppliedpressurecookerfigure` |
| `MatchesProblemReadouts` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-matchesproblemreadouts` |
| `UsesStandardNearEarthGravity` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-usesstandardnearearthgravity` |
| `UsesWaterSaturationTableAt120C` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-useswatersaturationtableat120c` |
| `SatisfiesBoilingAndPetcockBalanceLaws` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-satisfiesboilingandpetcockbalancelaws` |
| `AnswerChoice` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-answerchoice` |
| `displayedMassInGrams` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-displayedmassingrams` |
| `IsNearestDisplayedMass` | `def:physics:phyx-mini-0440:phyxminiproblems-problemphyxmini0440-isnearestdisplayedmass` |
| `problem_phyx_mini_0440` | `thm:physics:phyx_mini_0440:target` |

The Lean file already contained this declaration topology. Because the final
review rejection concerned only missing evidence, iteration 003 intentionally
preserved it unchanged.

## LeanExplore queries and candidates actually used

Every search below passed `packages: ["Mathlib", "Physlib"]`.

- Natural language: `dimensionful physical pressure and area quantities with
  SI unit readout`.
  Used candidates: `Dimensionful`, `UnitChoices.SI`.
- Natural language: `mass unit kilograms grams Dimensionful WithDim`.
  Used candidates: `MassUnit`, `MassUnit.grams`, `Dimensionful`.
- Natural language: `absolute temperature TemperatureUnit kelvin Celsius`.
  Used candidates: `Temperature`, `TemperatureUnit`,
  `TemperatureUnit.kelvin`.
- Natural language: `pressure force area and incipient lift force balance`.
  Used candidates: `DimPressure`, `DimArea`. The fluid-momentum and
  Newton's-second-law hits were too general to encode this apparatus law.
- Likely-name searches: `LengthUnit.millimeters`,
  `MassUnit.kilograms`, `WithDim`, and `DimArea`.
  Each exact intended declaration was found.

Fresh source and module data were fetched for the candidates actually used:

- `Dimensionful` — `Physlib.Units.Basic`;
- `WithDim` — `Physlib.Units.WithDim.Basic`;
- `DimPressure` — `Physlib.Units.WithDim.Pressure`;
- `DimArea` — `Physlib.Units.WithDim.Area`;
- `MassUnit`, `MassUnit.kilograms`, `MassUnit.grams` —
  `Physlib.ClassicalMechanics.Mass.MassUnit`;
- `Temperature` —
  `Physlib.Thermodynamics.Temperature.Basic`;
- `TemperatureUnit`, `TemperatureUnit.kelvin` —
  `Physlib.Thermodynamics.Temperature.TemperatureUnits`;
- `LengthUnit.millimeters` —
  `Physlib.SpaceAndTime.Space.LengthUnit`;
- `UnitChoices.SI` — `Physlib.Units.Basic`.

The fetched source confirms that `DimPressure` carries dimension
`M L⁻¹ T⁻²`, `DimArea` carries `L²`, and the named gram, kilogram,
millimetre, and kelvin declarations have the scales used by the readout
functions.

## PhysLean/Mathlib names grounded

- Dimensional core: `Dimensionful`, `WithDim`, `Dimension.M𝓭`,
  `Dimension.L𝓭`, `Dimension.T𝓭`, and `UnitChoices.SI`.
- Physical quantity APIs: `DimArea` and `DimPressure`.
- Named-unit APIs: `LengthUnit.meters`,
  `LengthUnit.millimeters`, `MassUnit.kilograms`,
  `MassUnit.grams`, and `TemperatureUnit.kelvin`.
- Absolute-temperature API: `Temperature` and `TemperatureUnit`.
- Mathlib supplies `ℝ`, `NNReal`, absolute value, finite inductive
  infrastructure, strings, and the algebraic/order notation used by the
  statement. No more specialized Mathlib theorem is needed at the
  autoformalization stage.

## Local abstractions introduced

- `MassQuantity` and `AccelerationQuantity` compose PhysLean's
  `Dimensionful (WithDim ... NNReal)` rather than erasing mass or
  acceleration to bare reals.
- `MeasuredTemperature` pairs PhysLean absolute `Temperature` with a
  zero-preserving storage unit. Celsius is an affine scalar readout, so the
  `273.15 K` offset is applied only in
  `temperatureInDegreesCelsius`.
- The named readout and force functions expose real numbers only after the
  physical quantity and unit have been specified.
- `WorkingFluid`, `PetcockState`, `FigureLabel`, `FigureRegion`,
  `PressureCookerFigure`, and `PressureCookerSetup` retain apparatus,
  phase, figure, and independent-quantity roles that library scalar types do
  not express.
- The scenario, figure, data, calibration, and governing-law structures keep
  logically distinct sources of assumptions separate.
- `AnswerChoice`, `displayedMassInGrams`, and
  `IsNearestDisplayedMass` faithfully represent the multiple-choice layer
  without assuming D.

## Grounding gaps

- LeanExplore found no pressure-cooker-specific saturation/incipient-lift API.
  The closest fluid momentum-balance and Newton's-second-law declarations are
  generic and do not encode the cooker geometry or the opposed outside
  pressure. The local
  `SatisfiesBoilingAndPetcockBalanceLaws` interface is therefore necessary
  and states the physical laws directly.
- No PhysLean steam-table dataset or cited table edition/row was found. The
  `198.5 kPa` saturated-water value is consequently modeled transparently
  as an independent thermodynamic calibration premise, not hidden in a
  definition and not confused with answer B's `198.5 g`.
- PhysLean's temperature units preserve zero and do not directly model the
  affine Celsius scale, so the local measured-temperature/readout layer is
  necessary.
- No redraft request: these gaps are faithfully exposed as calibration or law
  interfaces, and none imports the current mass/choice conclusion.

## Verification

- Lean LSP diagnostics: exactly one expected warning,
  `declaration uses sorry`, at the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0440.lean`: exit code 0
  with only the same expected warning.
- Full default `lake build`: exit code 0 (`Build completed successfully`).
  The problem file is not registered as its own Lake target
  (`lake build PhyXMiniProblems.problem_phyx_mini_0440` reports
  `unknown target`), so the direct `lake env lean` check above is the
  file-specific compilation evidence.
- No `/- USER: ... -/` file-specific hint is present.
- The blueprint contains `% archon:physics`.
- All declaration environments are ready for the deterministic
  `sync_leanok` phase. The blueprint was not edited because prover write
  permissions explicitly prohibit blueprint changes.
