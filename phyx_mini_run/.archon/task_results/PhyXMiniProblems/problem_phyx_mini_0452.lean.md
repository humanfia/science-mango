# Autoformalization result: `problem_phyx_mini_0452.lean`

## Assumption/target split

### Governing laws

- `SatisfiesWaterPropertyModel` states constitutive water-property lookups: the initial saturated-vapor pressure, specific volume, and specific internal energy come from the saturation table, while the final region and specific internal energy come from the table at the independently determined final pressure and specific volume.
- `SatisfiesMassSpecificPropertyLaws` states `V = m v` and `U = m u` at both endpoint states in coherent readouts.
- `SatisfiesLinearSpringPistonAndWorkLaws` states endpoint/path incidence, affine pressure and volume along the quasistatic process, piston sweep `ΔV = A Δx`, incremental static Hooke balance `Δp A = k Δx`, and straight-path boundary work `W = (p₁+p₂)(V₂-V₁)/2`.
- `SatisfiesClosedSystemFirstLaw` states the closed-system sign convention `Q_into = U₂ - U₁ + W_by`.

### Previous-part results

- None. The source report records no previous parts.

### Figure/data readouts

- `MatchesClosedSpringPistonWaterScenario` records a closed water sample, initially saturated vapor, heat addition, upward piston motion, a movable frictionless piston, a quasistatic process, a linear Hookean spring, and a linear pressure-volume path.
- `MatchesPrimarySpringPistonFigure` records the objects and geometry visible in `452.png`: enclosing rigid cylinder walls, water below a horizontal piston, a spring above it, the `H₂O` label, and spring attachment from the piston upper face to the fixed top support. The raster supplies no numerical process data.
- `MatchesProblemReadouts` records exactly the prose values: `m = 0.5 kg`, `T₁ = 120 °C`, `k = 15 kN/m`, `A = 0.05 m²`, and `p₂ = 500 kPa`.
- `MatchesReferenceSteamTableData` records independent rounded water-property calibrations used by the textbook computation: `p_sat(120 °C) = 198.53 kPa`, `v_g = 0.8919 m³/kg`, `u₁ = 2529.1 kJ/kg`, and the interpolated final `u₂ = 3668.1 kJ/kg`, together with final-state classification as superheated vapor.
- `HasPhysicalSpringPistonParameters` selects the positive physical branch.

### Current target conclusions

- `initialPressure_in_kilopascals` derives the initial pressure `198.53 kPa` from saturation data.
- `boundaryWork_in_kilojoules` derives `W_by = 17.548819925 kJ`.
- `internalEnergyChange_in_kilojoules` derives `ΔU = 569.5 kJ`.
- `problem_phyx_mini_0452` derives `Q = 587.048819925 kJ` and proves that `587 kJ`, answer D, is the unique closest displayed choice.

## Goal-faithfulness audit

No premise field contains the requested heat transfer, the numerical value `587 kJ`, an answer-choice equality, or `IsUniqueClosestDisplayedHeat`. Heat and work are independent `DimEnergy` fields of the physical setup, rather than local definitions made from the answer. The steam-table premises supply material properties (`p`, `v`, `u`) only; the target heat still requires piston kinematics, Hooke balance, boundary work, mass-specific-energy conversion, and the first law. `recordedDatasetAnswer` is metadata and is not accepted by any theorem or lemma. The substantive target is not true by unfolding any local definition.

The final exact rational is the result of the stated rounded calibration model:

- `ΔV = A² (p₂-p₁) / k = 0.050245 m³`;
- `W_by = 17.548819925 kJ`;
- `ΔU = 0.5 (3668.1-2529.1) = 569.5 kJ`;
- `Q = 587.048819925 kJ`.

Thus the formalization treats the displayed `587 kJ` as a rounded multiple-choice value by a unique-closest relation, rather than asserting that the unrounded physical calculation is definitionally or exactly `587`.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0452:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0452.problem_phyx_mini_0452`.
- Supporting derived declarations: `initialPressure_in_kilopascals`, `boundaryWork_in_kilojoules`, and `internalEnergyChange_in_kilojoules`.
- Physical carriers/readouts: `MassQuantity`, `LengthQuantity`, `VolumeQuantity`, `SpecificVolumeQuantity`, `SpecificEnergyQuantity`, `SpringConstantQuantity`, the named SI readout functions, and `CelsiusTemperatureReading`.
- Model vocabulary: `ProcessState`, `WorkingSubstance`, `WaterRegion`, `SpringModel`, `FigureObject`, `FigureTextLabel`, `SpringEndpoint`, `SpringPistonFigure`, `ThermodynamicState`, `WaterPropertyTable`, and `SpringPistonWaterProcess`.
- Premise structures: `MatchesClosedSpringPistonWaterScenario`, `MatchesPrimarySpringPistonFigure`, `MatchesProblemReadouts`, `HasPhysicalSpringPistonParameters`, `SatisfiesWaterPropertyModel`, `MatchesReferenceSteamTableData`, `SatisfiesMassSpecificPropertyLaws`, `SatisfiesLinearSpringPistonAndWorkLaws`, and `SatisfiesClosedSystemFirstLaw`.
- Answer metadata/target relation: `AnswerChoice`, `displayedHeatInKilojoules`, `recordedDatasetAnswer`, and `IsUniqueClosestDisplayedHeat`.

## LeanExplore grounding

Queries actually issued with `packages: ["Mathlib", "Physlib"]`:

- `thermodynamics first law heat internal energy boundary work`
- `spring-loaded piston Hooke law pressure volume work`
- `physical quantity SI dimensions pressure volume energy mass temperature`
- `PhysLean PhysicalQuantity SIUnit`
- `Temperature absolute thermodynamic temperature Physlib`
- `MassUnit kilograms Physlib`
- `DimArea physical area`

Candidates inspected and used:

- `DimEnergy` (ID 394468), from `Physlib.Units.WithDim.Energy`.
- `DimPressure` (ID 394474), from `Physlib.Units.WithDim.Pressure`.
- `UnitChoices.SI` (ID 394270), from `Physlib.Units.Basic`.
- `Dimension` (ID 394292), from `Physlib.Units.Dimension`.
- `Temperature` (ID 394201), from `Physlib.Thermodynamics.Temperature.Basic`.
- `DimArea` (ID 394411), from `Physlib.Units.WithDim.Area`.
- `WithDim` (ID 394425), from `Physlib.Units.WithDim.Basic`.
- `MassUnit.kilograms` (ID 385377) confirmed the SI mass-unit grounding used through `UnitChoices.SI`.

Near misses not used:

- `IdealGas.ideal_gas_law` is inappropriate because the working substance is real water and the computation depends on saturation/superheated steam tables.
- `MicroHamiltonian.internalU` and `CanonicalEnsemble.heatCapacity` concern statistical-mechanical models and do not provide the macroscopic closed-system first law needed here.
- `ClassicalMechanics.HarmonicOscillator.lagrangian_eq` does not model static force balance or piston sweep in a spring-loaded cylinder.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `L𝓭`, `T𝓭`, `M𝓭`, `UnitChoices.SI`, `DimArea`, `DimPressure`, `DimPressure.pascal`, `DimEnergy`, `DimEnergy.joule`, and `Temperature`.
- Mathlib: `NNReal`, `Set.Icc`, real absolute value notation, rational numerals, and the finite/decidable derivations used for state and answer labels.

## Local abstractions introduced

- `WaterPropertyTable` is the smallest local interface needed to preserve saturation and superheated-water constitutive roles absent from the available Physlib search results. It returns dimensionful pressure, specific volume, and specific energy rather than scalar placeholders.
- `CelsiusTemperatureReading` attaches an affine Celsius readout to Physlib's absolute `Temperature` with the exact `273.15 K` calibration.
- `SpringPistonFigure` preserves the labels and relative geometry of the primary raster without embedding numerical physics.
- `SpringPistonWaterProcess` keeps the apparatus, endpoint states, path, internal energies, heat, work, piston geometry, and material table as independent physical data.
- The premise structures separate source facts, figure evidence, table calibration, physical-domain conditions, constitutive laws, mechanics, and the first law so that none can hide the requested answer.

## Grounding gaps and redraft requests

- LeanExplore found no Physlib declaration for a macroscopic closed-system first law, quasistatic piston boundary work, a spring-loaded piston apparatus, or water/steam property tables. Faithful local law/property interfaces were therefore necessary.
- The blueprint gives only the source statement and recorded option, not the steam-table entries or interpolation that explain it. The plan agent should add the independent values and calculation route (including the precision convention) to the informal proof. In particular, it should confirm the intended `u₂` interpolation behind the recorded `587 kJ` answer.
- Internet source verification of the steam-table entries was attempted but the browsing endpoint was unavailable in this run; the formalization makes all rounded calibrations explicit so they can be reviewed or replaced without changing the governing-law split.
- The blueprint theorem environment was not marked `\leanok` because the explicit task write permissions prohibit editing blueprint chapters. A coordinator with blueprint write authority should add the marker after reviewing this formalization.

## Verification

- `archon-lean-lsp` diagnostics: only four expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0452.lean`: succeeds with the same four expected warnings and no errors.
- `git diff --check -- PhyXMiniProblems/problem_phyx_mini_0452.lean`: clean.
