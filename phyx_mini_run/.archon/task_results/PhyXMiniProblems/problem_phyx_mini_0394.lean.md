# Autoformalization result: `problem_phyx_mini_0394.lean`

## Assumption/target split

### Governing laws

- `SatisfiesFigureLiftGeometry` states that the physical vertical lift is the
  top-floor elevation minus the water-main elevation.
- `SatisfiesIdealPumpPressureRiseLaw` states the general pump relation
  `p_discharge = p_main + Δp_pump` and identifies the lossless,
  steady-incompressible regime.
- `SatisfiesHydrostaticRiserLaw` states the general vertical-riser balance
  `p_top = p_discharge - ρ g Δz`.
- `UsesStandardWaterAndGravity` supplies the independent room-temperature
  water-density calibration `998 kg/m³` and school-level gravity calibration
  `9.8 m/s²`. These values give an unrounded pump increment of
  `1,115,962 Pa = 1,115.962 kPa`, which rounds to the recorded `1116 kPa`.
- `HasPhysicalWaterlineParameters` records positivity and that the pump adds a
  nonnegative pressure increment.

### Previous-part results

- None. The source report lists no previous parts, and the blueprint dependency
  label has no usable locally queried ancestor information because the
  `archon` executable was not available on `PATH` in this runtime.

### Figure/data readouts

- `MatchesStatedProblemData` records water as the working fluid, a common gauge
  pressure reference, `600 kPa` at the main, and the required `200 kPa` at the
  top-floor line.
- `MatchesPrimaryBuildingFigure` records the main and pump at `-5 m`, ground at
  `0 m`, outlet `H` at `150 m`, the printed `150 m` and `5 m` markers, all five
  visible labels, the two pipe connections, upward flow, and multiple floors.
- `TallBuildingWaterlineFigure` and the label/location/pipe-segment inductives
  preserve the geometry and named entities read from image `394.png`.
- `displayedPressureKilopascals` records choices A--D, while
  `recordedAnswerChoice` separately records dataset metadata choice B.

### Current target conclusions

- The main theorem concludes that the total lift is `155 m`.
- It concludes that the independently stored pump pressure increment is
  `1,115,962 Pa`.
- It concludes that this pressure rounds to the displayed value attached to
  recorded answer B, namely `1116 kPa`.

## Goal-faithfulness audit

`pumpAddedPressure` is an independent field of
`TallBuildingWaterlineSetup`; it is not defined from `1116`, an answer choice,
or the desired conclusion. No premise structure states its numerical value or
states that it rounds to B. The pump-law premise only relates supply,
discharge, and pump increment, and the hydrostatic-law premise only relates
the discharge/top pressures through `ρ g Δz`. The stated `600 kPa` and
`200 kPa` values are boundary data from the question, while the `-5 m` and
`150 m` elevations are primary-figure readouts. `RoundsToNearestKilopascal` is
a generic half-open rounding predicate and contains no problem-specific answer.
Thus the requested pump pressure remains entirely on the conclusion side.

The exact `1115.962 kPa` result is retained before rounding, so the formalization
does not silently identify the rounded answer choice with an exact hydraulic
calculation.

## Declarations and blueprint correspondence

- `TallBuildingWaterlineFigure`: structured transcription of primary image
  `394.png`.
- `TallBuildingWaterlineSetup`: independent apparatus and physical quantities.
- `MatchesStatedProblemData`, `MatchesPrimaryBuildingFigure`,
  `UsesStandardWaterAndGravity`, and `HasPhysicalWaterlineParameters`: source,
  figure, calibration, and physical-domain assumptions.
- `SatisfiesFigureLiftGeometry`, `SatisfiesIdealPumpPressureRiseLaw`, and
  `SatisfiesHydrostaticRiserLaw`: geometry and governing physical laws.
- `totalVerticalLiftInMeters`: helper consequence `Δz = 155 m`.
- `requiredPumpAddedPressureInPascals`: helper consequence
  `Δp_pump = 1,115,962 Pa`.
- `problem_phyx_mini_0394`: corresponds to
  `thm:physics:phyx_mini_0394:target` and states the derived lift, exact pressure
  increment, rounding relation, and recorded displayed value.

The blueprint chapter was not edited to add `\leanok`, because the task's
write-permission section explicitly permits edits only to the assigned Lean
file and this task-result file.

## LeanExplore queries and candidates

All queries used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `physical pressure quantity with SI units pascal
  kilopascal` found `DimPressure`, `DimPressure.pascal`, and `UnitChoices.SI`.
- Natural-language queries `hydrostatic pressure difference density gravity
  height` and `hydrostatic equation pressure head` found the dimensional
  pressure API but no ready hydrostatic-balance declaration.
- Likely-name query `Dimensionful SI Pressure pascal` found `Dimensionful`,
  `DimPressure`, `DimPressure.pascal`, `UnitChoices.SI`, and `WithDim`.
- Likely-name query `DimLength meter` found `Dimension.L𝓭` and the more
  specialized `LengthUnit.meters`, but no ready `DimLength` type matching this
  task.
- Natural-language queries `DimMassDensity kilogram per cubic meter` and
  `DimAcceleration meter per second squared` found dimensional infrastructure;
  `FluidDynamics.MassDensity` was a near miss because it is a spatial scalar
  field rather than a unit-independent constant density quantity.
- Likely-name query `kilopascal` found `DimPressure` and
  `DimPressure.pascal`, but no dedicated kilopascal constant.

Source/module records fetched for declarations actually used in the design:

- `DimPressure` (`Physlib.Units.WithDim.Pressure`), declaration id `394474`.
- `Dimensionful` (`Physlib.Units.Basic`), declaration id `394284`.
- `WithDim` (`Physlib.Units.WithDim.Basic`), declaration id `394425`.
- `Dimension.L𝓭` (`Physlib.Units.Dimension`), declaration id `394324`.
- `UnitChoices.SI` (`Physlib.Units.Basic`), declaration id `394270`.
- `DimPressure.pascal` was inspected (id `394475`) to confirm the coherent-SI
  pressure convention, although direct SI readout was more convenient here.
- `FluidDynamics.MassDensity` was inspected (id `386034`) and rejected as the
  field-valued near miss described above.

## Physlib/Mathlib names grounded

- Physlib: `DimPressure`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`,
  `Dimension.M𝓭`, `Dimension.T𝓭`, and `UnitChoices.SI`.
- Mathlib: `NNReal`, `ℝ`, products, ordered real inequalities, and rational
  numeral notation used for coherent-SI readouts and rounding bounds.

## Local abstractions introduced

- `LengthQuantity`, `ElevationQuantity`, `MassDensityQuantity`, and
  `AccelerationQuantity` instantiate Physlib's dimensional infrastructure with
  the appropriate dimensions. Signed elevation is distinguished from
  nonnegative length so that the below-ground `-5 m` datum remains physical.
- Hydraulic locations, labels, pipe segments, pressure reference, and flow
  regime are small inductive types preserving the figure's semantic roles.
- The three law structures preserve pump and hydrostatic meaning because no
  matching high-level Physlib declaration was found. Their equations are
  general relations and do not contain the requested answer.
- The coherent-SI readout functions expose only named scalar measurements; the
  underlying physical quantities remain dimensionful.

## Grounding gaps and redraft requests

- No Mathlib/Physlib hydrostatic pressure-head or ideal pump pressure-rise law
  was returned by LeanExplore, so faithful local law predicates were required.
- Physlib has no directly matching constant mass-density or acceleration
  quantity aliases and no dedicated kilopascal constant in the searched API.
- The blueprint chapter contains `% archon:physics` but only a generic
  autoformalization instruction, not the promised informal physical derivation.
  A future plan-agent redraft should state the assumed water-density/gravity
  convention and whether pressures are intended as gauge pressures. The present
  formalization makes both choices explicit and retains the unrounded result.
- `/root/proposal_for_physic/science-mango/phyx_mini_run/.archon/AGENTS.md` was
  absent. The supplied prover prompt and `.archon/prover-modes/physics-formalize.md`
  were therefore used as the role specification.
- `archon dag-query` could not be run because `archon` was not available on
  `PATH`; no dependency was guessed.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0394.lean` exited with code
zero. The only diagnostics are the three expected `declaration uses sorry`
warnings for the two helper lemmas and the final theorem.
