# Autoformalization result: `problem_phyx_mini_0447.lean`

## Assumption/target split

### Governing laws

- `SatisfiesCoolingPistonLaws.circularCrossSection` states the circular-piston
  area relation `A = pi (d/2)^2`, and `cylindricalGasVolume` states `V = A h`
  at each modeled state.
- `pistonWeightLaw` states `W = m g` using explicit SI readouts of physical
  mass, acceleration, and force quantities.
- `fixedHeightUntilRelease` captures the constant-volume first phase while the
  upper stops remain engaged.
- `initialStopForceBalance` states that initial gas pressure supports
  atmospheric loading, piston weight, and a positive downward stop reaction.
- `freePistonForceBalanceDuringDescent` states the constant-load equilibrium
  relation `P A = P0 A + W` at release and at the final ambient-temperature
  state.
- `idealGasEquation` states `P V = n R T` at all three states of the same
  closed air sample.
- `pistonDropIsHeightDecrease` is the kinematic definition of the independent
  displacement observable as initial height minus final height; it assigns no
  numerical answer.
- `HasPhysicalCoolingPistonParameters` supplies positivity and nondegeneracy
  conditions for the physical quantities.
- `ReachesAmbientTemperature` identifies the event at which the requested
  displacement is measured by equating final air and ambient absolute
  temperatures.

### Previous-part results

- None. The source report records `previous_parts: []`, and the blueprint
  chapter declares no previous subproblem result.

### Figure/data readouts

- `MatchesProblemReadouts` records the prose data: initial pressure `250 kPa`,
  initial temperature `300 °C`, piston mass `50 kg`, piston diameter `0.1 m`,
  atmospheric pressure `100 kPa`, and ambient temperature `20 °C`.
- `PistonCylinderFigure`, `FigureObject`, `FigureLabel`, and
  `MatchesSuppliedPistonCylinderFigure` preserve the primary raster's cylinder
  walls, horizontal piston, enclosed air region, upper stops, `P0` label,
  downward `g` arrow, and initial-height arrow. The figure-derived scalar
  readout is exactly the initial gas-column height `25 cm`.
- `MatchesCoolingPistonScenario` records the closed air sample, vertical
  circular cylinder, initial stop support, freely sliding descent, cooling by
  heat transfer to ambient, and negligible friction.
- `UsesTextbookPhysicalConstants` calibrates `g = 9.81 m/s^2` and
  `R = 8.314 J/(mol K)` independently of the answer.
- `displayedDropCentimeters` preserves all four printed answer values, while
  `recordedDatasetAnswer` preserves the source metadata label D. Neither is a
  field of a governing law or a premise about the physical drop.

### Current target conclusions

- `pistonDropFormulaInMeters` concludes the general endpoint displacement
  formula obtained from ideal-gas behavior, cylinder geometry, final piston
  force balance, and the ambient-temperature event.
- `problem_phyx_mini_0447` concludes that the independently modeled physical
  drop rounds to the recorded `5.3 cm` display to the nearest tenth of a
  centimetre and that D is strictly closer than every alternative display.

## Goal-faithfulness audit

The setup stores pressure, area, length, volume, mass, acceleration, force,
and absolute temperature as physical quantities, not transparent real-number
aliases. The physical piston drop and every state's gas-column height are
independent fields. No setup field, data predicate, figure predicate,
positivity predicate, endpoint predicate, or law predicate assigns the final
height, `5.3 cm`, or answer D to the drop.

The only displacement relation among the assumptions is the general
kinematic identity saying that downward travel equals the decrease in column
height. The mechanical and thermodynamic laws are likewise general in the
apparatus quantities. The displayed answer table and recorded metadata label
do not constrain the physical setup. Therefore the numerical rounding and
unique-choice claims remain exclusively on the conclusion side of
`problem_phyx_mini_0447`; they cannot be obtained by unfolding a fake answer
definition or projecting a target-valued premise.

## Declarations created and blueprint mapping

- Blueprint label `thm:physics:phyx_mini_0447:target` is formalized by
  `PhyXMiniProblems.ProblemPhyXMini0447.problem_phyx_mini_0447`.
- The supporting derived target is
  `PhyXMiniProblems.ProblemPhyXMini0447.pistonDropFormulaInMeters`.
- Dimensionful quantities/readouts: `LengthQuantity`, `VolumeQuantity`,
  `MassQuantity`, `AccelerationQuantity`, `ForceQuantity`, the named SI
  readout functions, and Celsius/Kelvin conversion functions.
- Process/apparatus vocabulary: `ProcessState`, `EnclosedGas`,
  `CylinderOrientation`, `CylinderCrossSection`, `PistonSupportRegime`,
  `ThermalProcess`, `GasState`, and `CoolingPistonSetup`.
- Figure vocabulary: `VerticalDirection`, `FigureObject`, `FigureLabel`,
  `PistonCylinderFigure`, and `MatchesSuppliedPistonCylinderFigure`.
- Assumption predicates: `MatchesCoolingPistonScenario`,
  `MatchesProblemReadouts`, `UsesTextbookPhysicalConstants`,
  `HasPhysicalCoolingPistonParameters`, `ReachesAmbientTemperature`, and
  `SatisfiesCoolingPistonLaws`.
- Answer representation: `AnswerChoice`, `displayedDropCentimeters`,
  `recordedDatasetAnswer`, `RoundsToNearestTenthCentimeter`, and
  `IsUniqueClosestChoice`.

The theorem environment is ready for project-managed `\lean{...}` and
`\leanok` synchronization. I did not edit the blueprint because the explicit
write-permission list makes blueprint chapters read-only for this prover lane.

## LeanExplore queries/candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `physical pressure with dimensions pascal` returned
  `DimPressure`, `DimPressure.pascal`, and related Physlib pressure units.
- Natural-language query `physical area with dimensions` returned `DimArea`.
- Natural-language query `absolute temperature kelvin TemperatureUnit`
  returned `Temperature`, `TemperatureUnit`, and `TemperatureUnit.kelvin`.
- Likely-name query `Dimensionful WithDim` returned `Dimensionful` and its
  unit-scaling infrastructure.
- Exact/likely-name queries `Temperature.toReal` and
  `DimArea DimPressure UnitChoices.SI` confirmed the readout declarations
  used in the file.
- Natural-language query `ideal gas law pressure volume temperature piston
  cylinder` returned `IdealGas.ideal_gas_law`. Its source and docstring show
  that it is explicitly unitless, uses real variables, and fixes `R = 1`, so
  it is incompatible with this file's dimensionful apparatus and explicit SI
  `R` calibration.
- Natural-language query `piston static force balance atmospheric pressure
  weight` returned `FluidDynamics.FluidInMomentumBalance`; its source is a
  general continuum-fluid state/stress/body-force carrier, not a ready-made
  quasistatic piston equilibrium theorem.
- Source and module data were fetched only for candidates used or seriously
  evaluated: `DimPressure` (ID 394474), `DimArea` (394411), `Temperature`
  (394201), `TemperatureUnit.kelvin` (394250), `Dimensionful` (394284),
  `Temperature.toReal` (394203), `UnitChoices.SI` (394270),
  `IdealGas.ideal_gas_law` (393919), and
  `FluidDynamics.FluidInMomentumBalance` (386040).

## Physlib/Mathlib names grounded

- Physlib `DimPressure` from `Physlib.Units.WithDim.Pressure` represents
  pressure with dimension `M L^-1 T^-2`.
- Physlib `DimArea` from `Physlib.Units.WithDim.Area` represents physical area
  with dimension `L^2`.
- Physlib `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.M𝓭`, and
  `Dimension.T𝓭` retain the length, volume, mass, acceleration, and force
  roles of locally composed quantity types.
- Physlib `Temperature`, `Temperature.toReal`, `TemperatureUnit`, and
  `TemperatureUnit.kelvin` ground nonnegative absolute temperature and kelvin
  readouts; Celsius is applied only as an affine scalar readout.
- Physlib `UnitChoices.SI` supplies metres, seconds, kilograms, coulombs, and
  kelvin as the coherent SI unit choice.
- Mathlib real arithmetic, `Real.pi`, absolute value, and finite enumeration
  support the circular geometry and multiple-choice rounding statements.

## Local abstractions introduced

- Length, volume, mass, acceleration, and force use the smallest local
  `Dimensionful (WithDim d NNReal)` compositions needed because the searched
  Physlib APIs did not expose convenient named aliases for every apparatus
  quantity. These preserve dimensions and nonnegativity rather than reducing
  physical primitives to scalar aliases.
- `AmountOfSubstance` remains an abstract carrier with an explicit mole
  readout. This preserves its physical role while avoiding a fake real alias;
  Physlib's found ideal-gas theorem is unitless and does not provide a
  dimensionful amount/R interface compatible with this setup.
- `SatisfiesCoolingPistonLaws` is a faithful local governing-law interface for
  cylinder geometry, piston mechanics, stop engagement/release, and the
  fixed-sample ideal-gas equation. It was introduced because no searched API
  packages these laws for a quasistatic piston/cylinder process.
- Figure enums and `PistonCylinderFigure` preserve semantic image labels and
  spatial roles without treating the bitmap as untyped data.
- `RoundsToNearestTenthCentimeter` explicitly distinguishes the continuous
  predicted displacement from the one-decimal answer display.

## Grounding gaps and redraft requests

- No compatible ready-made Mathlib/Physlib model for a stop-supported piston,
  its release force balance, or the complete two-phase cooling process was
  found, so the local law interface is necessary.
- `IdealGas.ideal_gas_law` is a near miss rather than reusable infrastructure:
  it is a unitless statistical-mechanics result with `R = 1`, whereas the
  source problem uses dimensionful pressure, volume, temperature, amount, and
  the SI gas constant.
- The blueprint proof paragraph contains workflow instructions rather than an
  informal physics derivation. A plan-agent redraft should state that the
  piston remains at `25 cm` until `P = P0 + mg/A`, then moves at that constant
  pressure; applying the fixed-sample ideal-gas relation from the initial to
  final states gives a final height about `19.68 cm` and hence a drop about
  `5.32 cm`, selecting D.
- The requested `.archon/AGENTS.md` is absent in this checkout. The injected
  physics-formalize role instructions and established project conventions
  supplied the role requirements.
- The advertised `archon` executable is not on `PATH`, so the optional DAG
  queries could not run. The source report independently records no previous
  parts, and the chapter declares no dependency edges beyond its target.
- The assigned Lean file did not exist initially, so it contained no
  file-specific `/- USER: ... -/` comments to apply.
- The blueprint exists and contains `% archon:physics`, but its `\leanok`
  marker was not added because this task's explicit write permissions forbid
  edits to blueprint chapters.

## Verification

- `archon-lean-lsp` diagnostics report no errors or failed dependencies and
  exactly two expected `declaration uses sorry` warnings, one for each
  substantive theorem body.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0447.lean` exits with code
  0 and reports the same two expected warnings.
