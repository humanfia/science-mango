import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0450

open Dimension

/-!
# Boundary work of water under a linear spring-loaded piston

A sealed piston/cylinder contains `2 kg` of liquid water initially at
`20 °C` and `300 kPa`. Heating raises the pressure to `3 MPa` when the
volume reaches `0.1 m³`. A linear spring loads the movable piston, so the
quasistatic pressure--volume path is affine.

Mass, volume, specific volume, pressure, temperature, and work are represented
by dimensionful physical quantities. Real numbers occur only as calibrated
readouts in named units, as the scalar graph of pressure against an SI volume
readout, and as displayed answer-choice values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of specific volume, `L³ M⁻¹`. -/
def specificVolumeDimension : Dimension := volumeDimension * M𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative, unit-independent thermodynamic specific volume. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim specificVolumeDimension NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical volume in the cube of a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read specific volume in cubic selected-length-units per selected mass unit. -/
def specificVolumeReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Kilogram readout used in the problem statement. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Cubic-metre readout used in the problem statement. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- Cubic metres per kilogram, used for the liquid-water table datum. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  specificVolumeReadout MassUnit.kilograms LengthUnit.meters specificVolume

/-- Read dimensionful pressure in coherent SI units (pascals). -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal pressure readout used for the initial state. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Megapascal pressure readout used for the final state. -/
def pressureInMegapascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000000

/-- Read dimensionful work/energy in coherent SI units (joules). -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Kilojoule work readout used by the answer choices. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-!
Physlib represents absolute temperature, whereas degrees Celsius form an
affine scale. This interface couples a Celsius observation to the same
absolute physical temperature through `T_K = T_°C + 273.15`.
-/
structure CelsiusTemperatureReading where
  absoluteTemperature : Temperature
  degreesCelsius : ℝ
  celsiusKelvinCalibration :
    absoluteTemperature.toReal = degreesCelsius + 5463 / 20

/-! ## Water states, process, and figure-derived information -/

/-- The two endpoints of the heating process. -/
inductive ProcessEndpoint where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- Substance contained below the piston. -/
inductive FluidSubstance where
  | water
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic region of a water state. -/
inductive WaterRegion where
  | compressedLiquid
  | saturatedMixture
  | superheatedVapor
  | other
  deriving DecidableEq, Repr

/-- Idealized process regime needed for equilibrium boundary work. -/
inductive ProcessRegime where
  | quasistaticHeatingAgainstLinearSpring
  | other
  deriving DecidableEq, Repr

/-- Sign convention selected by the positive recorded answer. -/
inductive WorkSignConvention where
  | doneByWater
  | doneOnWater
  deriving DecidableEq, Repr

/-- One equilibrium state of the water. -/
structure WaterState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : CelsiusTemperatureReading
  specificVolume : SpecificVolumeQuantity
  region : WaterRegion

/--
External compressed-liquid water data. Its lookup returns a physical
specific volume from physical pressure and absolute temperature inputs.
-/
structure LiquidWaterPropertyTable where
  specificVolumeAt :
    DimPressure → Temperature → SpecificVolumeQuantity

/-- Objects plainly visible in the supplied piston/cylinder raster. -/
inductive FigureObject where
  | cylinderWalls
  | movablePiston
  | helicalSpring
  | blueWaterRegion
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels shown in the supplied raster. -/
inductive FigureLabel where
  | referencePressureP0
  | waterH2O
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and symbolic evidence carried by the primary figure. The
reference-pressure symbol `P₀` denotes a physical pressure but supplies no
numerical pressure, volume, temperature, or work readout.
-/
structure SpringPistonCylinderFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  pressureDenotedByP0 : DimPressure
  springAbovePiston : Bool
  waterBelowPiston : Bool
  pistonSpansCylinder : Bool
  springMountedBetweenCylinderTopAndPiston : Bool
  waterRegionIsBlue : Bool
  containsQuantitativeScaleOrStateReadout : Bool

/-!
The complete physical setup. The process pressure function is an SI scalar
readout of physical pressure as a function of an SI cubic-metre readout; it is
not itself used as a replacement for either physical quantity.
-/
structure SpringPistonWaterSetup where
  contents : FluidSubstance
  waterMass : MassQuantity
  stateAt : ProcessEndpoint → WaterState
  waterTable : LiquidWaterPropertyTable
  outsideReferencePressureP0 : DimPressure
  figure : SpringPistonCylinderFigure
  processRegime : ProcessRegime
  workSignConvention : WorkSignConvention
  processPressureInPascals : ℝ → ℝ
  workDoneByWater : DimEnergy
  sealedToMassTransfer : Bool
  pistonIsMovable : Bool
  springIsLinear : Bool
  waterIsHeated : Bool

/-! ## Assumptions: scenario, readouts, figure, reference data, and laws -/

/-- Qualitative facts stated or conventionally idealized in the scenario. -/
structure MatchesSpringPistonWaterScenario
    (setup : SpringPistonWaterSetup) : Prop where
  contentsAreWater : setup.contents = .water
  initialStateIsLiquidWater :
    (setup.stateAt .initial).region = .compressedLiquid
  closedWaterSystem : setup.sealedToMassTransfer = true
  movablePiston : setup.pistonIsMovable = true
  linearSpring : setup.springIsLinear = true
  heatingProcess : setup.waterIsHeated = true
  quasistaticLinearSpringRegime :
    setup.processRegime = .quasistaticHeatingAgainstLinearSpring
  positiveExpansionWorkConvention :
    setup.workSignConvention = .doneByWater

/-!
The five numerical readouts explicitly supplied by the prose. In particular,
neither the initial volume nor the requested work is included here.
-/
structure MatchesProblemReadouts (setup : SpringPistonWaterSetup) : Prop where
  waterMassKilograms : massInKilograms setup.waterMass = 2
  initialTemperatureDegreesCelsius :
    (setup.stateAt .initial).temperature.degreesCelsius = 20
  initialPressureKilopascals :
    pressureInKilopascals (setup.stateAt .initial).pressure = 300
  finalPressureMegapascals :
    pressureInMegapascals (setup.stateAt .final).pressure = 3
  finalVolumeCubicMeters :
    volumeInCubicMeters (setup.stateAt .final).volume = 1 / 10

/-- Exact qualitative geometry and labels visible in the supplied image. -/
structure MatchesSuppliedSpringPistonFigure
    (setup : SpringPistonWaterSetup) : Prop where
  everyDepictedObjectIsShown :
    ∀ object, setup.figure.objectShown object = true
  everyPrintedLabelIsShown :
    ∀ label, setup.figure.labelShown label = true
  P0DenotesOutsideReferencePressure :
    setup.figure.pressureDenotedByP0 = setup.outsideReferencePressureP0
  springIsAbovePiston : setup.figure.springAbovePiston = true
  waterIsBelowPiston : setup.figure.waterBelowPiston = true
  pistonCrossesCylinderBore : setup.figure.pistonSpansCylinder = true
  springConnectsTopAndPiston :
    setup.figure.springMountedBetweenCylinderTopAndPiston = true
  waterFillIsBlue : setup.figure.waterRegionIsBlue = true
  noQuantitativeScaleOrStateReadout :
    setup.figure.containsQuantitativeScaleOrStateReadout = false

/-!
The initial specific volume is supplied by a constitutive compressed-liquid
water table, rather than being defined from the requested work.
-/
structure SatisfiesInitialLiquidWaterStateRelation
    (setup : SpringPistonWaterSetup) : Prop where
  initialSpecificVolumeFromTable :
    (setup.stateAt .initial).specificVolume =
      setup.waterTable.specificVolumeAt
        (setup.stateAt .initial).pressure
        (setup.stateAt .initial).temperature.absoluteTemperature

/-!
Reference property data needed to make the numerical exercise determinate:
liquid water at `20 °C` has specific volume approximately
`0.001002 m³/kg`; pressure dependence over this compressed-liquid range is
neglected at the precision of the answer choices.
-/
structure MatchesReferenceLiquidWaterData
    (setup : SpringPistonWaterSetup) : Prop where
  initialTableSpecificVolumeCubicMetersPerKilogram :
    specificVolumeInCubicMetersPerKilogram
        (setup.waterTable.specificVolumeAt
          (setup.stateAt .initial).pressure
          (setup.stateAt .initial).temperature.absoluteTemperature) =
      501 / 500000

/-- Positivity and endpoint ordering for the physical expansion. -/
structure HasPhysicalSpringPistonParameters
    (setup : SpringPistonWaterSetup) : Prop where
  massPositive : 0 < massInKilograms setup.waterMass
  pressurePositive :
    ∀ endpoint, 0 < pressureInPascals (setup.stateAt endpoint).pressure
  volumePositive :
    ∀ endpoint, 0 < volumeInCubicMeters (setup.stateAt endpoint).volume
  specificVolumePositive :
    ∀ endpoint,
      0 < specificVolumeInCubicMetersPerKilogram
        (setup.stateAt endpoint).specificVolume
  outsideReferencePressurePositive :
    0 < pressureInPascals setup.outsideReferencePressureP0
  volumeIncreases :
    volumeInCubicMeters (setup.stateAt .initial).volume <
      volumeInCubicMeters (setup.stateAt .final).volume
  pressureIncreases :
    pressureInPascals (setup.stateAt .initial).pressure <
      pressureInPascals (setup.stateAt .final).pressure

/-!
Conservation of water mass and `V = m v` for each equilibrium endpoint, stated
in arbitrary coherent mass/length units. It does not assign the requested
work a value.
-/
structure SatisfiesClosedWaterMassVolumeLaw
    (setup : SpringPistonWaterSetup) : Prop where
  endpointMassVolumeRelation :
    ∀ (endpoint : ProcessEndpoint) (massUnit : MassUnit)
        (lengthUnit : LengthUnit),
      volumeReadout lengthUnit (setup.stateAt endpoint).volume =
        massReadout massUnit setup.waterMass *
          specificVolumeReadout massUnit lengthUnit
            (setup.stateAt endpoint).specificVolume

/-!
A linear spring makes equilibrium pressure affine in piston displacement and
hence affine in cylinder volume. This specifies the whole path from the
independently supplied endpoint states, without mentioning work or an answer.
-/
structure SatisfiesLinearSpringPressurePath
    (setup : SpringPistonWaterSetup) : Prop where
  pressureIsAffineOnProcessInterval :
    ∀ volume : ℝ,
      volume ∈ Set.Icc
          (volumeInCubicMeters (setup.stateAt .initial).volume)
          (volumeInCubicMeters (setup.stateAt .final).volume) →
        setup.processPressureInPascals volume =
          pressureInPascals (setup.stateAt .initial).pressure +
            (pressureInPascals (setup.stateAt .final).pressure -
                pressureInPascals (setup.stateAt .initial).pressure) /
              (volumeInCubicMeters (setup.stateAt .final).volume -
                volumeInCubicMeters (setup.stateAt .initial).volume) *
              (volume -
                volumeInCubicMeters (setup.stateAt .initial).volume)
  pressureAtInitialEndpoint :
    setup.processPressureInPascals
        (volumeInCubicMeters (setup.stateAt .initial).volume) =
      pressureInPascals (setup.stateAt .initial).pressure
  pressureAtFinalEndpoint :
    setup.processPressureInPascals
        (volumeInCubicMeters (setup.stateAt .final).volume) =
      pressureInPascals (setup.stateAt .final).pressure

/-!
For a closed, quasistatic piston/cylinder process, boundary work done by the
water is the signed path integral `∫ p dV` in coherent SI readouts. This is a
general governing law and contains no numerical work conclusion.
-/
structure SatisfiesQuasistaticBoundaryWorkLaw
    (setup : SpringPistonWaterSetup) : Prop where
  boundaryWorkIntegral :
    energyInJoules setup.workDoneByWater =
      ∫ volume in
          volumeInCubicMeters (setup.stateAt .initial).volume..
          volumeInCubicMeters (setup.stateAt .final).volume,
        setup.processPressureInPascals volume

/-! ## Derived quantities and answer metadata -/

/-- Labels printed beside the four candidate work values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Work in kilojoules printed beside each answer label. -/
def displayedWorkInKilojoules : AnswerChoice → ℝ
  | .A => 376 / 5
  | .B => 600
  | .C => 27 / 5
  | .D => 1617 / 10

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement after reporting work to the one decimal place used in the list. -/
def IsReportedWorkChoice
    (setup : SpringPistonWaterSetup) (choice : AnswerChoice) : Prop :=
  round (10 * energyInKilojoules setup.workDoneByWater) =
    round (10 * displayedWorkInKilojoules choice)

/-- A choice is the only displayed value agreeing with the reported work. -/
def IsUniqueReportedWorkChoice
    (setup : SpringPistonWaterSetup) (choice : AnswerChoice) : Prop :=
  IsReportedWorkChoice setup choice ∧
    ∀ other, IsReportedWorkChoice setup other → other = choice

/-!
The water table and `V = m v` give the independently derived initial volume
`V₁ = 2(0.001002) = 0.002004 m³`.
-/
lemma initialVolumeInCubicMeters
    (setup : SpringPistonWaterSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hState : SatisfiesInitialLiquidWaterStateRelation setup)
    (hPropertyData : MatchesReferenceLiquidWaterData setup)
    (hMassVolume : SatisfiesClosedWaterMassVolumeLaw setup) :
    volumeInCubicMeters (setup.stateAt .initial).volume =
      501 / 250000 := by
  change volumeReadout LengthUnit.meters (setup.stateAt .initial).volume = _
  rw [hMassVolume.endpointMassVolumeRelation .initial
    MassUnit.kilograms LengthUnit.meters]
  change massInKilograms setup.waterMass *
    specificVolumeInCubicMetersPerKilogram
      (setup.stateAt .initial).specificVolume = _
  rw [hReadouts.waterMassKilograms, hState.initialSpecificVolumeFromTable,
    hPropertyData.initialTableSpecificVolumeCubicMetersPerKilogram]
  norm_num

/-!
Integrating the affine pressure path yields the trapezoid area under the
pressure--volume curve. This remains a symbolic consequence of the two
governing laws and contains no answer-choice value.
-/
lemma linearSpringBoundaryWork_endpointAverage
    (setup : SpringPistonWaterSetup)
    (hPhysical : HasPhysicalSpringPistonParameters setup)
    (hPath : SatisfiesLinearSpringPressurePath setup)
    (hWorkLaw : SatisfiesQuasistaticBoundaryWorkLaw setup) :
    energyInJoules setup.workDoneByWater =
      (pressureInPascals (setup.stateAt .initial).pressure +
          pressureInPascals (setup.stateAt .final).pressure) / 2 *
        (volumeInCubicMeters (setup.stateAt .final).volume -
          volumeInCubicMeters (setup.stateAt .initial).volume) := by
  rw [hWorkLaw.boundaryWorkIntegral]
  let a := volumeInCubicMeters (setup.stateAt .initial).volume
  let b := volumeInCubicMeters (setup.stateAt .final).volume
  let p := pressureInPascals (setup.stateAt .initial).pressure
  let q := pressureInPascals (setup.stateAt .final).pressure
  change (∫ x in a..b, setup.processPressureInPascals x) =
    (p + q) / 2 * (b - a)
  have hab : a < b := by
    simpa [a, b] using hPhysical.volumeIncreases
  have hcongr :
      (∫ x in a..b, setup.processPressureInPascals x) =
        ∫ x in a..b, p + (q - p) / (b - a) * (x - a) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hPath.pressureIsAffineOnProcessInterval
    simpa [Set.uIcc_of_le hab.le, a, b] using hx
  rw [hcongr]
  have hp : IntervalIntegrable (fun _ : ℝ => p) MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable _ _
  have hs : IntervalIntegrable
      (fun x : ℝ => (q - p) / (b - a) * (x - a))
      MeasureTheory.volume a b :=
    (continuous_const.mul
      (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hp hs]
  rw [intervalIntegral.integral_const]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub
    intervalIntegral.intervalIntegrable_id
    (continuous_const.intervalIntegrable _ _)]
  rw [integral_id, intervalIntegral.integral_const]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  field_simp [hba]
  ring

/-!
Using the endpoint readouts and the liquid-water initial volume, the exact
model value is `161.6934 kJ` before answer-list rounding.
-/
lemma workDoneByWaterInKilojoules_exact
    (setup : SpringPistonWaterSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hState : SatisfiesInitialLiquidWaterStateRelation setup)
    (hPropertyData : MatchesReferenceLiquidWaterData setup)
    (hPhysical : HasPhysicalSpringPistonParameters setup)
    (hMassVolume : SatisfiesClosedWaterMassVolumeLaw setup)
    (hPath : SatisfiesLinearSpringPressurePath setup)
    (hWorkLaw : SatisfiesQuasistaticBoundaryWorkLaw setup) :
    energyInKilojoules setup.workDoneByWater = 808467 / 5000 := by
  have hV₁ :=
    initialVolumeInCubicMeters setup hReadouts hState hPropertyData hMassVolume
  have hW :=
    linearSpringBoundaryWork_endpointAverage setup hPhysical hPath hWorkLaw
  have hp₁ :
      pressureInPascals (setup.stateAt .initial).pressure = 300000 := by
    have h := hReadouts.initialPressureKilopascals
    rw [pressureInKilopascals] at h
    linarith
  have hp₂ :
      pressureInPascals (setup.stateAt .final).pressure = 3000000 := by
    have h := hReadouts.finalPressureMegapascals
    rw [pressureInMegapascals] at h
    linarith
  rw [energyInKilojoules, hW, hp₁, hp₂,
    hReadouts.finalVolumeCubicMeters, hV₁]
  norm_num

/-!
The spring-loaded expansion therefore does `161.6934 kJ` of boundary work by
the water, reported as `161.7 kJ`. This uniquely selects choice D.

This formalizes `thm:physics:phyx_mini_0450:target`. No premise fixes the
requested work value or selects an answer choice.
-/
theorem problem_phyx_mini_0450
    (setup : SpringPistonWaterSetup)
    (hScenario : MatchesSpringPistonWaterScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedSpringPistonFigure setup)
    (hState : SatisfiesInitialLiquidWaterStateRelation setup)
    (hPropertyData : MatchesReferenceLiquidWaterData setup)
    (hPhysical : HasPhysicalSpringPistonParameters setup)
    (hMassVolume : SatisfiesClosedWaterMassVolumeLaw setup)
    (hPath : SatisfiesLinearSpringPressurePath setup)
    (hWorkLaw : SatisfiesQuasistaticBoundaryWorkLaw setup) :
    energyInKilojoules setup.workDoneByWater = 808467 / 5000 ∧
      IsUniqueReportedWorkChoice setup .D := by
  have hExact := workDoneByWaterInKilojoules_exact setup hReadouts hState
    hPropertyData hPhysical hMassVolume hPath hWorkLaw
  refine ⟨hExact, ?_⟩
  unfold IsUniqueReportedWorkChoice IsReportedWorkChoice
  constructor
  · rw [hExact]
    norm_num [displayedWorkInKilojoules]
  · intro other hOther
    rw [hExact] at hOther
    fin_cases other <;>
      norm_num [displayedWorkInKilojoules] at hOther
    rfl

end PhyXMiniProblems.ProblemPhyXMini0450
