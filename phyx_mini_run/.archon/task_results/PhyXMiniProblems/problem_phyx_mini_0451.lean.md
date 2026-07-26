# Autoformalization result: `problem_phyx_mini_0451.lean`

## Iteration 003 review disposition

The iteration-002 gate reason was evidence-only: no genuine post-formalization
task result existed for the revised Lean model. I re-audited that model against
the source report, the primary image `451.png`, the physics blueprint, the
installed Physlib/Mathlib APIs, and the current `physics-formalize` rules. No
semantic redraft was required, so the existing physical statement was retained
unchanged. This file is the requested post-formalization evidence report.

The blueprint contains `% archon:physics`, so the physics-formalize discipline
applies.

## Assumption/target split

### Governing laws

- `SatisfiesRigidVesselWaterLaws.massConservation` and
  `constantOccupiedVolume` state conservation of the fixed water inventory and
  rigidity of the occupied volume.
- `massSpecificVolumeLaw` states `V = m v` independently at each endpoint.
- `saturatedMixtureClassification` classifies a state as a saturated
  liquid-vapor mixture when its specific volume lies between the saturated
  liquid and saturated vapor values at the same temperature.
- `saturatedMixtureQualityBounds` gives the physical mass-fraction bounds
  `0 <= x <= 1` for a saturated mixture.
- `saturatedMixtureSpecificVolumeLaw` states
  `v = v_f + x (v_g - v_f)`.
- `saturatedMixtureSpecificInternalEnergyLaw` states
  `u = u_f + x u_fg`.
- `closedSystemFirstLaw` states the sign-convention-specific relation
  `Delta U = Q - W_by` using total endpoint internal energies `m u`.
- `rigidBoundaryWorkIsZero` states that the rigid boundary does no boundary
  work. None of these fields contains the requested heat, final quality, or
  answer label.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and no result
  from another part is assumed.

### Figure/data readouts and calibrations

- `MatchesRigidWaterVesselScenario` records water, constant-volume heating, a
  rigid closed vessel, negligible kinetic/potential-energy changes, a closed
  outlet valve, and an initially saturated mixture.
- Direct inspection of `phyx_data/test_image/451.png` supports
  `MatchesSuppliedFigure`: a rectangular vessel, blue water inventory below a
  headspace, four burner flames below the vessel on a manifold, and a top
  outlet that bends right through a circular crossed valve symbol. The bitmap
  supplies no numerical thermodynamic property or heat answer.
- `MatchesProblemReadouts` records the source values `m_1 = 2 kg`,
  `T_1 = 120 degC`, `x_1 = 1/4`, and `T_2 = T_1 + 20 degC`.
- `MatchesReferenceSaturatedWaterData` is an explicitly separate external
  steam-table calibration. It records `v_f`, `v_g`, `u_f`, and `u_fg` at the
  two independently fixed endpoint temperatures in `m^3/kg` and `kJ/kg`.
  It mentions neither heat transfer nor an answer choice.
- `displayedHeatInKilojoules` transcribes all four printed choices, while
  `recordedDatasetAnswer := .D` stores dataset metadata and is not a theorem
  premise.

### Current target conclusions

Only `heat_transfer_to_rigid_water_vessel` concludes:

- the final phase is a saturated liquid-vapor mixture;
- the final vapor quality is `9891 / 22552`;
- the independently modeled heat readout is
  `98980769 / 112760 kJ` (approximately `877.80036 kJ`);
- choice D reports that heat to one decimal place; and
- D is the unique displayed choice satisfying that reporting relation.

## Goal-faithfulness audit

`RigidWaterVesselSetup.heatTransferredToWater` is an independent `DimEnergy`
field. It is not defined from `877.8`, choice D, the exact target fraction, or
the candidate table. The first-law premise relates it only to independent
endpoint mass/internal-energy observables and boundary work.

No premise structure contains the final quality `9891 / 22552`, the exact heat
`98980769 / 112760`, `IsReportedHeatChoice setup .D`, or uniqueness of D.
`MatchesReferenceSaturatedWaterData` contains constitutive water-property
calibrations, not the sought process heat; deriving the heat still requires
constant volume, both mixture interpolation laws, mass conservation, and the
closed-system first law. `IsReportedHeatChoice` is a generic relation between
an independently modeled heat and any displayed choice, so unfolding it does
not make D true.

The arithmetic was independently checked from the stated calibration:

- `v_1 = 53/50000 + (1/4)(89133/100000 - 53/50000)
       = 89451/400000 m^3/kg`;
- constant specific volume gives
  `x_2 = (v_1 - 27/25000) / (1017/2000 - 27/25000)
       = 9891/22552`;
- `u_1 = 12587/25 + (1/4)(50644/25) = 25248/25 kJ/kg`;
- the final mixture energy and `Q = 2 (u_2 - u_1)` give
  `Q = 98980769/112760 kJ`, approximately `877.80036 kJ`.

Thus the target is a substantive consequence of the law/data interface, not
an assumption or a definition-by-unfolding.

## Declarations and blueprint correspondence

- Target theorem `PhyXMiniProblems.ProblemPhyXMini0451.heat_transfer_to_rigid_water_vessel`
  corresponds to `thm:physics:phyx_mini_0451:target`.
- Dimension declarations `volumeDimension`, `specificVolumeDimension`, and
  `specificInternalEnergyDimension` correspond to the blueprint topology
  labels ending in `-volumedimension`, `-specificvolumedimension`, and
  `-specificinternalenergydimension`.
- Physical quantity declarations `MassQuantity`, `VolumeQuantity`,
  `SpecificVolumeQuantity`, and `SpecificInternalEnergyQuantity` correspond to
  the labels ending in `-massquantity`, `-volumequantity`,
  `-specificvolumequantity`, and `-specificinternalenergyquantity`.
- Named readouts `massInKilograms`, `volumeInCubicMetres`,
  `specificVolumeInCubicMetresPerKilogram`,
  `specificInternalEnergyInJoulesPerKilogram`,
  `specificInternalEnergyInKilojoulesPerKilogram`, `energyInJoules`, and
  `energyInKilojoules` correspond to their same normalized names under the
  prefix `def:physics:phyx-mini-0451:phyxminiproblems-problemphyxmini0451-`.
- `MeasuredTemperature`, `temperatureInKelvins`, and
  `temperatureInDegreesCelsius` correspond to the three temperature topology
  labels of those normalized names.
- Physical/figure vocabulary `WorkingFluid`, `ProcessStage`,
  `WaterPhaseRegion`, `ProcessKind`, `ValveStatus`, `FigureObject`,
  `RigidVesselFigure`, `WaterState`, `SaturatedWaterTable`, and
  `RigidWaterVesselSetup` correspond one-for-one to the blueprint definition
  labels of the same normalized names.
- Premise interfaces `MatchesRigidWaterVesselScenario`,
  `MatchesSuppliedFigure`, `MatchesProblemReadouts`,
  `MatchesReferenceSaturatedWaterData`, and `SatisfiesRigidVesselWaterLaws`
  correspond one-for-one to their listed blueprint definition labels.
- Answer vocabulary `AnswerChoice`, `displayedHeatInKilojoules`,
  `recordedDatasetAnswer`, and `IsReportedHeatChoice` corresponds one-for-one
  to the final four blueprint definition labels.

The blueprint already lists all of these exact `\lean{...}` names. It was not
edited to add `\leanok`, because this task's explicit write-permission section
forbids editing blueprint chapters. A coordinator with blueprint write access
should add `\leanok` to the accepted target environment.

## LeanExplore queries and candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `dimensionful physical quantities with unit choices
  and dimensions` returned and grounded `Dimensionful` (id `394284`) and the
  surrounding unit-scaling API.
- Natural-language queries `closed thermodynamic system first law rigid vessel
  heat internal energy boundary work`, `thermodynamic first law closed system
  heat boundary work internal energy`, and `saturated water steam table vapor
  quality mixture specific volume internal energy` returned
  `MicroHamiltonian.internalU`, `IdealGas.ideal_gas_law`, ideal-gas adiabatic
  relations, and `DimEnergy`, but no closed-system first-law, saturated-water
  table, or two-phase quality interpolation interface suitable for this model.
- Likely-name query `Dimensionful WithDim DimEnergy` returned
  `Dimensionful` (id `394284`), `WithDim` (id `394425`), and related
  dimension-tagging declarations. Exact query `DimEnergy` grounded
  `DimEnergy` (id `394468`).
- Likely-name queries `Temperature`, `Temperature TemperatureUnit
  MassUnit.kilograms LengthUnit.meters`, and `TemperatureUnit.kelvin` grounded
  `Temperature` (id `394201`), `Temperature.toReal` (id `394203`),
  `TemperatureUnit` (id `394233`), `TemperatureUnit.kelvin` (id `394250`),
  and `UnitChoices.SI` (id `394270`).
- Queries `LengthUnit meters physical unit` and `MassUnit kilograms physical
  unit` grounded `LengthUnit.meters` (id `393154`) and
  `MassUnit.kilograms` (id `385377`).
- Query `Real.round` grounded Mathlib `round` (id `99909`), whose checked
  source rounds to the nearest integer with ties toward positive infinity.

Source, module, and docstring information was fetched for the candidates
actually used: `Dimensionful`, `WithDim`, `DimEnergy`, `UnitChoices.SI`,
`Temperature`, `Temperature.toReal`, `TemperatureUnit`,
`TemperatureUnit.kelvin`, `MassUnit.kilograms`, `LengthUnit`,
`LengthUnit.meters`, and `round`.

## Physlib/Mathlib names grounded

- Physlib dimensional infrastructure: `Dimension`, `Dimension.L𝓭`,
  `Dimension.M𝓭`, `Dimension.T𝓭`, `Dimensionful`, `WithDim`, and
  `UnitChoices.SI`.
- Physlib energy: `DimEnergy`, with dimension `M L^2 T^-2`.
- Physlib units: `MassUnit.kilograms`, `LengthUnit.meters`,
  `TemperatureUnit`, and `TemperatureUnit.kelvin`.
- Physlib temperature: `Temperature` and `Temperature.toReal`.
- Mathlib carriers/operations: `NNReal`, `Real`/`ℝ`, finite inductive types,
  ordered real arithmetic, rational numeral notation, and `round`.

Lean LSP local search independently confirmed `Dimensionful`, `WithDim`,
`DimEnergy`, `Temperature`, `TemperatureUnit`, and `round` in the installed
checkout. Compilation confirms all qualified unit names used in the file.

## Local abstractions introduced

- `MassQuantity`, `VolumeQuantity`, `SpecificVolumeQuantity`, and
  `SpecificInternalEnergyQuantity` specialize Physlib's unit-independent
  `Dimensionful (WithDim ...)` infrastructure at the correct physical
  dimensions. They are not transparent scalar aliases.
- `MeasuredTemperature` couples Physlib's nonnegative absolute `Temperature`
  magnitude to its zero-preserving storage unit; the affine Celsius offset is
  introduced only in a named real readout.
- The water-state, phase, process, valve, figure, setup, and saturated-table
  types preserve the physical roles and the primary raster vocabulary rather
  than collapsing the problem to unrelated real scalars.
- `SaturatedWaterTable` and `SatisfiesRigidVesselWaterLaws` are minimal local
  interfaces because the searches found no reusable two-phase water-table or
  macroscopic closed-system first-law API. Their fields state constitutive data
  and general physical laws, not the requested answer.
- `AnswerChoice` and `IsReportedHeatChoice` preserve the multiple-choice
  display and its one-decimal reporting semantics without using the recorded
  label to determine the modeled heat.

## Grounding gaps and redraft requests

- LeanExplore exposed no suitable Physlib/Mathlib saturated-water property
  table, vapor-quality interpolation law, or macroscopic closed-system first
  law. The dimensionally faithful local interfaces are therefore necessary.
- The extracted source and current source report do not cite a steam-table
  edition for the endpoint property rows. The theorem makes those rows an
  explicit external calibration premise rather than presenting them as figure
  data or hiding them in the target. A future source/blueprint pass should cite
  the intended table edition if bibliographic grounding is required.
- The requested `.archon/AGENTS.md` is absent. The available complete role file
  `.archon/prover-modes/physics-formalize.md` was read and followed instead.
- No `/- USER: ... -/` comment is present in the assigned Lean file.
- The prompt-advertised `archon` executable is not on `PATH`, so both requested
  DAG queries failed with `archon: command not found`. The source report still
  establishes that there are no previous parts.

## Verification

- Pre-report `archon-lean-lsp` diagnostics reported one expected
  `declaration uses sorry` warning at the target theorem and no errors or
  failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0451.lean` exited with code
  0 and emitted only the same expected `declaration uses sorry` warning.
