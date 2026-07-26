# Proof result: `problem_phyx_mini_0439.lean`

## Completed

- `final_specific_volume_after_opening_valve` is proof-closed with no
  `sorry`, `admit`, or new axiom.
- The proof derives `m_A = 2 kg`, rewrites tank B's volume as
  `(7/2) v_B`, and applies rigid-volume additivity, mass conservation, and
  the final `V = m v` law to prove
  `v_f = (2 + 7 v_B) / 11`.
- In iteration 018 the proof body was rewritten as an explicit typed
  derivation with named SI-readout equalities and a final `calc` chain. The
  theorem signature and all hypotheses remain unchanged.

## Assumption/target split

### Governing laws

- `SatisfiesRigidTankMassVolumeLaws.initialTankMassVolumeLaw`: each rigid tank obeys `V = m v` in every coherent mass/length unit choice.
- `rigidTotalVolumeLaw`: after opening the valve, the total occupied volume is the sum of the two fixed tank volumes.
- `totalMassConservationLaw`: the closed pair's final mass is the sum of its two initial masses.
- `finalMassVolumeLaw`: the uniform final condition obeys `V_total = m_total v_final`.
- `MatchesTwoTankWaterScenario` records that both contents are water, the valve changes from closed to open, the combined system is closed, both walls are rigid, and the final state is uniform.
- `HasPhysicalTwoTankParameters` records positivity only; it contains no exact final-value relation.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- Primary image `phyx_data/test_image/439.png`: tank `A` is left of tank `B`; the two rectangular tanks are joined by a horizontal pipe with a central circular crossed valve; both tanks have blue contents.
- Source readouts: tank `A` has `p_A = 200 kPa`, `v_A = 1/2 m³/kg`, and `V_A = 1 m³`; tank `B` has `m_B = 7/2 kg`, `p_B = 500 kPa`, and `T_B = 400 °C`.
- The displayed values A `0.4500`, B `0.6173`, C `0.5000`, and D `0.5746`, plus recorded answer D, are represented only by `AnswerChoice`, `displayedSpecificVolumeInCubicMetersPerKilogram`, and `recordedDatasetAnswer` metadata.
- Neither the source report nor the image identifies a water-property table edition or row for the specific volume at `0.5 MPa, 400 °C`.

### Current target conclusion

- `final_specific_volume_after_opening_valve` concludes the strongest source-supported relation
  `v_final = (2 + 7 * v_B) / 11` in cubic metres per kilogram, where `v_B` is tank B's initial physical specific-volume readout.
- No numerical final value and no answer-choice correctness or uniqueness claim is concluded.

## Goal-faithfulness audit

The exact target relation appears only in the theorem conclusion. The premise structures contain qualitative scenario/figure facts, the six stated readouts, positivity, and the independent laws `V = m v`, rigid volume addition, and mass conservation. In particular, `finalMassVolumeLaw` relates final volume, mass, and specific volume without assigning the requested expression to any of them.

The rejected constitutive premise `v_B = 0.6173 m³/kg` was removed. The theorem no longer assumes a table row, superheated-region classification, numerical final specific volume, rounding result, or answer label. The occurrence of `6173 / 10000` is confined to answer-choice B metadata from the source and is disconnected from the theorem.

## Declarations and blueprint labels

All names below are in `PhyXMiniProblems.ProblemPhyXMini0439`.

- `volumeDimension` ↔ `def:physics:phyx-mini-0439:phyxminiproblems-problemphyxmini0439-volumedimension`
- `specificVolumeDimension` ↔ `...-specificvolumedimension`
- `VolumeQuantity` ↔ `...-volumequantity`; `MassQuantity` ↔ `...-massquantity`; `SpecificVolumeQuantity` ↔ `...-specificvolumequantity`
- `volumeReadout` ↔ `...-volumereadout`; `massReadout` ↔ `...-massreadout`; `specificVolumeReadout` ↔ `...-specificvolumereadout`
- `volumeInCubicMeters` ↔ `...-volumeincubicmeters`; `massInKilograms` ↔ `...-massinkilograms`; `specificVolumeInCubicMetersPerKilogram` ↔ `...-specificvolumeincubicmetersperkilogram`
- `pressureInPascals` ↔ `...-pressureinpascals`; `pressureInKilopascals` ↔ `...-pressureinkilopascals`
- `CelsiusTemperatureReading` ↔ `...-celsiustemperaturereading`
- `TankLabel` ↔ `...-tanklabel`; `FluidSubstance` ↔ `...-fluidsubstance`; `ValveStatus` ↔ `...-valvestatus`
- `ThermodynamicState` ↔ `...-thermodynamicstate`; `RigidTank` ↔ `...-rigidtank`; `UniformFinalCondition` ↔ `...-uniformfinalcondition`; `TwoTankValveSetup` ↔ `...-twotankvalvesetup`
- `FigureObject` ↔ `...-figureobject`; `SuppliedTwoTankFigure` ↔ `...-suppliedtwotankfigure`
- `MatchesTwoTankWaterScenario` ↔ `...-matchestwotankwaterscenario`; `MatchesSuppliedTwoTankFigure` ↔ `...-matchessuppliedtwotankfigure`; `MatchesProblemReadouts` ↔ `...-matchesproblemreadouts`
- `HasPhysicalTwoTankParameters` ↔ `...-hasphysicaltwotankparameters`; `SatisfiesRigidTankMassVolumeLaws` ↔ `...-satisfiesrigidtankmassvolumelaws`
- `AnswerChoice` ↔ `...-answerchoice`; `displayedSpecificVolumeInCubicMetersPerKilogram` ↔ `...-displayedspecificvolumeincubicmetersperkilogram`; `recordedDatasetAnswer` ↔ `...-recordeddatasetanswer`
- `final_specific_volume_after_opening_valve` ↔ `thm:physics:phyx_mini_0439:target`

Here `...-suffix` abbreviates the shared label prefix `def:physics:phyx-mini-0439:phyxminiproblems-problemphyxmini0439`.

The semantic repair removed `WaterRegion`, `WaterPropertyTable`, `SatisfiesTankBWaterPropertyModel`, `MatchesReferenceWaterPropertyData`, and `IsReportedSpecificVolumeChoice`. Their old blueprint topology entries are stale because they encoded or supported the uncited constitutive value and numerical choice claim.

## LeanExplore grounding

Queries actually run with `packages: ["Mathlib", "Physlib"]`:

- `dimensionful physical quantities with units pressure mass length temperature`
- `DimPressure Dimensionful WithDim Temperature LengthUnit MassUnit`
- `water thermodynamic specific volume property table rigid tank mass conservation`
- `Temperature absolute physical temperature toReal`
- `LengthUnit MassUnit`
- `MassUnit.kilograms`
- `WithDim`
- `Dimension.M𝓭`

Candidates actually used and inspected (source, module, and docstring):

- `Dimensionful` from `Physlib.Units.Basic`
- `UnitChoices` and `UnitChoices.SI` from `Physlib.Units.Basic`
- `DimPressure` from `Physlib.Units.WithDim.Pressure`
- `Temperature` and `Temperature.toReal` from `Physlib.Thermodynamics.Temperature.Basic`
- `LengthUnit` / `LengthUnit.meters` from `Physlib.SpaceAndTime.Space.LengthUnit`
- `MassUnit` / `MassUnit.kilograms` from `Physlib.ClassicalMechanics.Mass.MassUnit`
- `WithDim` from `Physlib.Units.WithDim.Basic`
- `Dimension`, `Dimension.L𝓭`, and `Dimension.M𝓭` from `Physlib.Units.Dimension`

Near-miss search results not used were `RigidBodyMotion.massDistribution_mass`, `FluidDynamics.NavierStokes.ClassicalContinuityEquation`, and `IdealGas.ideal_gas_law`: they model rigid-body motion, continuum flow, or ideal gases rather than a closed two-water-tank valve process.

## Local abstractions

- `VolumeQuantity`, `MassQuantity`, and `SpecificVolumeQuantity` specialize Physlib's unit-independent `Dimensionful (WithDim _ NNReal)` rather than collapsing physical quantities to scalars.
- `CelsiusTemperatureReading` pairs Physlib's absolute nonnegative `Temperature` with the source's affine Celsius readout and its Kelvin calibration.
- Tank, valve, final-condition, and figure structures preserve the two labels, process status, independent physical fields, and raster geometry.
- `SatisfiesRigidTankMassVolumeLaws` is the smallest local interface for the four governing relations needed here because no matching Physlib closed-rigid-tank API was found.

## Redraft needed

- Original problem: `phyx_mini_0439`.
- Source report:
  `reports/phyx_mini/problem_phyx_mini_0439.source.json`.
- Theorem:
  `PhyXMiniProblems.ProblemPhyXMini0439.final_specific_volume_after_opening_valve`.
- The frozen Lean statement is provable and physically correct, but it proves
  only a symbolic conservation relation. It cannot be strengthened to the
  source's numerical choice D by changing the proof body: no current
  hypothesis determines tank B's initial specific volume from its
  `500 kPa`, `400 °C` readouts.
- The smallest self-contained numerical redraft is to add a calibrated
  property-data premise
  `specificVolumeInCubicMetersPerKilogram
    (setup.tank .B).initialState.specificVolume = 6173 / 10000`
  and change the conclusion to the exact final value
  `specificVolumeInCubicMetersPerKilogram
    setup.finalCondition.state.specificVolume = 63211 / 110000`.
  This value differs from displayed choice D, `2873 / 5000`, by
  `1 / 22000`, so it rounds to `0.5746`.
- To reproduce the blueprint contract literally, an authorized
  autoformalization/redraft pass should instead restore its modeled reference
  property premise and four-decimal reported-choice predicate, then conclude
  choice D. Those declaration/signature changes are outside this prover's
  proof-body-only permissions.
- This is also the exact blocker reported by the iteration-017 proof review.
  It cannot be repaired honestly in iteration 018 because the signature is
  frozen and this role may edit only the body after `:= by`.
- No Mathlib/Physlib equilibrium-water steam-table API or cited external
  property-table row is present in the project references. The numerical
  calibration must therefore be supplied as an explicit, traceable premise.
- The `archon` executable advertised for DAG navigation is not available on
  `PATH`; the chapter's explicit `\uses{}` topology was inspected directly.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0439.lean`: exit code 0
  after the iteration-018 body rewrite.
- Lean LSP: no errors; only unused-variable warnings for `hScenario`,
  `hFigure`, and `hPhysical`.
- `lean_verify` source scan: no warnings. The theorem uses only foundational
  axioms `propext`, `Classical.choice`, and `Quot.sound`.
- The blueprint was not edited or marked `\leanok` because the prover write
  permissions explicitly allow edits only to the assigned Lean file and this
  task-result file.
