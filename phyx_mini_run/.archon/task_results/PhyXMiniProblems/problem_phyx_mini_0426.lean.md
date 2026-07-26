# Autoformalization result: `problem_phyx_mini_0426.lean`

## Final-review disposition and evidence

The review gate's exact retry reason was evidence-only: it reported that the
generic physics-grounding preflight predated the revised Lean model and did not
establish the searches and modeling choices actually used.  I therefore
preserved the current physical statement after a fresh source/law/answer audit
and regenerated this post-formalization report from the assigned Lean file,
the complete `% archon:physics` blueprint chapter, the source JSON, and direct
inspection of `phyx_data/test_image/426.png`.

The primary raster visibly places states 2 and 3 on the same vertical line at
`40 cm³`.  Thus the Lean readout for state 2 is correctly `40 cm³`; the
auxiliary caption's `30 cm³` text is inconsistent with both the raster and its
own assertion that `2 → 3` is a constant-volume leg.

## Assumption/target split

### Governing laws

- `SatisfiesTriangularHeatEngineLaws.clockwiseTriangleBoundaryWork` states that positive work done by the gas in the clockwise triangular cycle is the enclosed pressure--volume area, with the pressure and volume read in coherent SI units.
- `SatisfiesTriangularHeatEngineLaws.shaftRateDeterminesCycleRate` relates the thermodynamic cycle frequency to the shaft rpm and the dimensionless number of cycles per shaft revolution.
- `SatisfiesTriangularHeatEngineLaws.averagePowerIsWorkPerCycleTimesCycleRate` states the general physical law `power = work per cycle * cycles per second`.
- The universal conversion lemmas connect atmospheres to pascals, cubic centimetres to cubic metres, and inverse minutes to inverse seconds. They are declarations to prove, not problem-specific assumptions.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and the formalization assumes no result from another subproblem.

### Figure/data readouts

- `MatchesDiatomicHeatEngineScenario` records that the device is a heat engine, the working gas is diatomic, the path is treated as a quasistatic equilibrium cycle, clockwise work is positive when done by the gas, and the stored absolute-temperature scale is kelvin.
- `MatchesProblemOperatingData` records the state-1 temperature as `20 °C`, the shaft speed as `500 rpm`, and the textbook coupling of one thermodynamic cycle per shaft revolution.
- `MatchesSuppliedPressureVolumeFigure` records the `V (cm³)` horizontal axis, `p (atm)` vertical axis, tick labels, state labels, arrows `1 → 2 → 3 → 1`, segment geometry, and the physical plotted coordinates.
- Primary-image inspection resolves the auxiliary-caption inconsistency: state 2 is at `(40 cm³, 1.5 atm)`, not `(30 cm³, 1.5 atm)`. This agrees with the visibly vertical `2 → 3` leg at `40 cm³`.
- `HasPhysicalHeatEngineParameters` records positivity and the nondegenerate positive width/height of the clockwise triangular cycle.

### Current target conclusions

- `netWorkDoneByGasPerCycle_eq`: the derived work per cycle is `12159 / 8000 J`.
- `thermodynamicCycleFrequencyInHertz_eq`: the derived cycle frequency is `25 / 3 Hz`.
- `problem_phyx_mini_0426`: the exact idealized output is `4053 / 320 W`; it rounds to `13 W`; and answer D is uniquely closest among the four displayed powers.

## Goal-faithfulness audit

The exact output `4053 / 320 W`, the nearest-watt statement, and the unique selection of D occur only in the conclusion of `problem_phyx_mini_0426`. They do not occur in `DiatomicHeatEngineSetup`, any scenario/data/figure/physicality premise, or `SatisfiesTriangularHeatEngineLaws`. The independent `averagePowerOutput` field is not defined from the desired answer; it is constrained only by the general law `P = W f`.

Likewise, the intermediate numerical work and cycle-frequency values occur only as conclusions of derived lemmas. The law structure contains symbolic relations among physical quantities and calibrated readouts, not those computed values. `recordedDatasetAnswer := .D` is isolated as source metadata and is not an input to the theorem or to the definition of output power.

The source's `13 W` is not asserted as a false exact equality. From the raster, the triangular area is `1.519875 J` and the rate is `500 / 60 Hz`, yielding the exact idealized value `12.665625 W`; the formalization therefore treats `13 W` as a nearest-whole-watt display and as the unique closest answer choice.

## Declarations and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0426:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0426.problem_phyx_mini_0426`.
- Blueprint labels `lem:physics:phyx-mini-0426:phyxminiproblems-problemphyxmini0426-networkdonebygaspercycle-eq` and `lem:physics:phyx-mini-0426:phyxminiproblems-problemphyxmini0426-thermodynamiccyclefrequencyinhertz-eq` correspond to `netWorkDoneByGasPerCycle_eq` and `thermodynamicCycleFrequencyInHertz_eq`.
- The three unit-conversion lemma labels correspond to `pressureInPascals_eq_atmospheres_mul_standardAtmosphere`, `volumeInCubicMeters_eq_cubicCentimeters_div_million`, and `frequencyInHertz_eq_perMinute_div_sixty`.
- `CycleState`, `CycleLeg`, `PressureVolumeFigure`, and the figure enums preserve the state numbers, axis roles/units, arrows, and line geometry visible in the supplied raster.
- `ThermodynamicStateData` and `DiatomicHeatEngineSetup` preserve physical state quantities, working-gas/device roles, work, two distinct frequencies, their coupling ratio, and output power.
- `MatchesDiatomicHeatEngineScenario`, `MatchesProblemOperatingData`, `MatchesSuppliedPressureVolumeFigure`, and `HasPhysicalHeatEngineParameters` partition qualitative assumptions, prose data, primary-image evidence, and physicality conditions.
- `SatisfiesTriangularHeatEngineLaws` contains only the governing physical relations.
- `netWorkDoneByGasPerCycle_eq` and `thermodynamicCycleFrequencyInHertz_eq` expose the two calculation stages needed by the final theorem.
- `AnswerChoice`, `displayedPowerInWatts`, `RoundsToNearestWatt`, and `IsUniqueClosestDisplayedPower` faithfully represent the multiple-choice display without using it to determine the physics.

The chapter already existed and contained `% archon:physics`. It was not edited to add `\leanok`, because this task's explicit write-permission section forbids editing blueprint chapters; the coordinator should add that marker after accepting the formalization.

## LeanExplore queries and candidates used

All searches used `packages: ["Mathlib", "Physlib"]`.

- `dimensionful physical quantity WithDim pressure energy units` and `DimPressure standardAtmosphere DimEnergy`: used `Dimensionful` (id 394284), `DimPressure` (id 394474), `DimPressure.standardAtmosphere` (id 394478), and `DimEnergy` (id 394468). Checked sources identify the unit-covariant subtype, pressure dimension `M L⁻¹ T⁻²`, energy dimension `M L² T⁻²`, and one standard atmosphere as exactly `101325` coherent SI pascals.
- `Temperature TemperatureUnit kelvin Celsius` and `Temperature Temperature.toReal physical absolute temperature`: used `Temperature` (id 394201), `TemperatureUnit` (id 394233), and `TemperatureUnit.kelvin` (id 394250). Checked sources confirm that `Temperature` stores a nonnegative absolute-temperature magnitude and kelvin has scale one. LSP hover additionally grounded `Temperature.toReal : Temperature → ℝ`. No affine Celsius object appeared, so Celsius is represented only as a calibrated scalar readout.
- `LengthUnit centimeters meters`, `LengthUnit.meters LengthUnit.centimeters`, and `LengthUnit centimeters meters TimeUnit seconds minutes`: used `LengthUnit.centimeters` (id 393160) and `LengthUnit.meters` (id 393154); checked sources confirm the exact `10⁻²` scale.
- `TimeUnit seconds minutes`, `TimeUnit.seconds TimeUnit.minutes`, and `LengthUnit centimeters meters TimeUnit seconds minutes`: used `TimeUnit.seconds` (id 393630), `TimeUnit.minutes` (id 393638), and the corroborating conversion lemma `TimeUnit.minutes_div_seconds` (id 393642); checked sources confirm the exact factor `60`.
- `thermodynamic boundary work pressure volume cycle average power`: returned `DimPressure`, `IdealGas.ideal_gas_law`, and `RigidBody.rigid_body_work_and_power`. The latter two are near misses: neither states signed pressure--volume-cycle area or heat-engine average power as work per cycle times cycle frequency.

## Physlib/Mathlib names grounded

- `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, and `UnitChoices.SI`.
- `DimPressure`, `DimPressure.standardAtmosphere`, and `DimEnergy`.
- `Temperature`, `Temperature.toReal`, `TemperatureUnit`, and `TemperatureUnit.kelvin`.
- `LengthUnit`, `LengthUnit.meters`, `LengthUnit.centimeters`, `TimeUnit`, `TimeUnit.seconds`, and `TimeUnit.minutes`.
- Mathlib `NNReal`, `ℝ`, `List`, absolute value, and rational arithmetic notation.

## Local abstractions introduced

- `VolumeQuantity := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)` preserves nonnegative physical volume and its length-cubed dimension.
- `FrequencyQuantity := Dimensionful (WithDim T𝓭⁻¹ NNReal)` preserves nonnegative inverse-time quantities for shaft and cycle rates.
- `PowerQuantity := Dimensionful (WithDim powerDimension NNReal)` preserves nonnegative output power with dimension `M L² T⁻³`.
- The setup, raster, and law structures are minimal interfaces for physical roles absent from the searched library. They do not wrap physical primitives as plain scalar aliases and do not contain the current target answer.

## Grounding gaps

- The relevant LeanExplore searches exposed no native Physlib `DimVolume`, dimensionful frequency, or `DimPower` declaration matching this use, so dimensionally faithful `Dimensionful` aliases were introduced locally.
- No matching library theorem was found for work as the signed area of this triangular pressure--volume cycle or for heat-engine power as work per cycle times cycle frequency. These therefore appear as explicit governing-law fields rather than guessed library names.
- The initial temperature and diatomic-gas character are faithfully retained even though the pressure--volume area already determines work and no amount of gas is provided; consequently the ideal-gas law is neither needed nor assumed.
- The requested `.archon/AGENTS.md` is absent. The complete user-supplied role instructions and `.archon/prover-modes/physics-formalize.md` were used instead.
- No `/- USER: ... -/` comment is present in the assigned Lean file.
- Although the task notes that `archon` is on `PATH`, both requested `archon dag-query` invocations failed with `archon: command not found`; the source report independently confirms that there are no previous parts.

## Verification

- `archon-lean-lsp` diagnostics: six expected `declaration uses sorry` warnings, no errors, no failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0426.lean`: exit code 0 with the same six expected warnings.
