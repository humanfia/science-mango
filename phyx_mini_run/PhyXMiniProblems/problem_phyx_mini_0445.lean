import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0445

open Dimension

/-!
# Nitrogen-gas volume flow from a falling liquid level

A constant-cross-section container holds liquid nitrogen at `100 K`. During
one hour, evaporation lowers the liquid level by `30 mm`. The resulting vapor
passes through the valve and heater shown in the supplied raster and leaves at
`500 kPa` and `260 K`.

The numerical unit text was lost from the extracted answer choices. The
recorded value `0.02526` is dimensionally and numerically consistent with
`m³/min`, using the nitrogen-property readouts `v_liquid = 0.001452 m³/kg`
at `100 K` and `v_exit = 0.1467 m³/kg` at `500 kPa`, `260 K`. Accordingly,
the answer-choice readouts below are explicitly interpreted as `m³/min`.

Physical lengths, areas, times, specific volumes, mass-flow rates,
volume-flow rates, pressures, and absolute temperatures remain typed physical
quantities. Real numbers occur only as calibrated unit readouts and displayed
multiple-choice values.

Assumption/target split:

* governing laws: liquid volume loss determines evaporated mass, mass is
  conserved through the valve and heater, and gas volume flow is mass flow
  times outlet specific volume;
* previous-part results: none;
* figure/data readouts: the container/valve/heater topology, `100 K`,
  `0.5 m²`, `30 mm`, `1 h`, `500 kPa`, `260 K`, and the two independent
  nitrogen property-table entries;
* current target: the exact flow implied by those rounded property data and
  its uniquely rounded answer-choice value `0.02526 m³/min` (choice D).
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of thermodynamic specific volume, `L³ M⁻¹`. -/
def specificVolumeDimension : Dimension := volumeDimension * M𝓭⁻¹

/-- The physical dimension of mass flow, `M T⁻¹`. -/
def massFlowRateDimension : Dimension := M𝓭 * T𝓭⁻¹

/-- The physical dimension of volume flow, `L³ T⁻¹`. -/
def volumeFlowRateDimension : Dimension := volumeDimension * T𝓭⁻¹

/-- A nonnegative physical length, used for the observed level drop. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative thermodynamic specific volume. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim specificVolumeDimension NNReal)

/-- A nonnegative mass-flow rate. -/
abbrev MassFlowRateQuantity : Type :=
  Dimensionful (WithDim massFlowRateDimension NNReal)

/-- A nonnegative volume-flow rate. -/
abbrev VolumeFlowRateQuantity : Type :=
  Dimensionful (WithDim volumeFlowRateDimension NNReal)

/-- Read a physical area in the square of the selected length unit. -/
def areaReadout (unit : LengthUnit) (area : DimArea) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in the selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a specific volume in cubic selected-length-units per mass unit. -/
def specificVolumeReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read a mass-flow rate in selected mass-units per selected time-unit. -/
def massFlowRateReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (massFlowRate : MassFlowRateQuantity) : ℝ :=
  ((massFlowRate {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Read a volume-flow rate in cubic length-units per selected time-unit. -/
def volumeFlowRateReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (volumeFlowRate : VolumeFlowRateQuantity) : ℝ :=
  ((volumeFlowRate {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an absolute temperature in kelvins from its zero-preserving unit. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Cubic metres per minute, the reconstructed unit of the answer list. -/
def volumeFlowInCubicMetersPerMinute
    (volumeFlowRate : VolumeFlowRateQuantity) : ℝ :=
  volumeFlowRateReadout LengthUnit.meters TimeUnit.minutes volumeFlowRate

/-- Cubic metres per kilogram, used for the two nitrogen property entries. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  specificVolumeReadout MassUnit.kilograms LengthUnit.meters specificVolume

/-!
These are general named-unit conversions. They contain no data about the
particular nitrogen system and no requested flow-rate value.
-/

lemma lengthInMeters_eq_millimeters_div_thousand
    (length : LengthQuantity) :
    lengthReadout LengthUnit.meters length =
      lengthReadout LengthUnit.millimeters length / 1000 := by
  let uMeters : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.meters}
  let uMillimeters : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.millimeters}
  have hscale : UnitChoices.dimScale uMeters uMillimeters L𝓭 = 1000 := by
    apply NNReal.eq
    norm_num [uMeters, uMillimeters, UnitChoices.dimScale,
      LengthUnit.millimeters, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val]
    rfl
  have h := length.property uMeters uMillimeters
  rw [show dim (WithDim L𝓭 NNReal) = L𝓭 by rfl, hscale] at h
  have hv := congrArg (fun x => ((x.val : NNReal) : ℝ)) h
  change lengthReadout LengthUnit.millimeters length =
    1000 * lengthReadout LengthUnit.meters length at hv
  rw [hv]
  ring

lemma timeInMinutes_eq_sixty_mul_hours (duration : TimeQuantity) :
    timeReadout TimeUnit.minutes duration =
      60 * timeReadout TimeUnit.hours duration := by
  let uHours : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.hours}
  let uMinutes : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.minutes}
  have hscale : UnitChoices.dimScale uHours uMinutes T𝓭 = 60 := by
    apply NNReal.eq
    norm_num [uHours, uMinutes, UnitChoices.dimScale, TimeUnit.hours,
      TimeUnit.minutes, TimeUnit.seconds, TimeUnit.scale,
      TimeUnit.div_eq_val]
    rfl
  have h := duration.property uHours uMinutes
  rw [show dim (WithDim T𝓭 NNReal) = T𝓭 by rfl, hscale] at h
  have hv := congrArg (fun x => ((x.val : NNReal) : ℝ)) h
  change timeReadout TimeUnit.minutes duration =
    60 * timeReadout TimeUnit.hours duration at hv
  exact hv

/-! ## Container, flow path, states, and supplied figure -/

/-- The working substance named in the problem. -/
inductive WorkingSubstance where
  | nitrogen
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic phases relevant to the liquid container and outlet. -/
inductive MatterPhase where
  | liquid
  | vapor
  | gas
  deriving DecidableEq, Repr

/-- The mechanism stated to lower the liquid level. -/
inductive LevelDropCause where
  | evaporationDueToHeatTransfer
  | other
  deriving DecidableEq, Repr

/-- The two labeled regions inside the left-hand container. -/
inductive ContainerRegion where
  | liquidRegion
  | vaporRegion
  deriving DecidableEq, Fintype, Repr

/-- Major objects visible along the left-to-right flow path. -/
inductive FigureObject where
  | container
  | valve
  | heater
  | outletArrow
  deriving DecidableEq, Fintype, Repr

/-- Literal text labels visible in the supplied raster. -/
inductive FigureTextLabel where
  | vapor
  | liquidN2
  | heater
  deriving DecidableEq, Fintype, Repr

/-- The three directed flow segments visible in the raster. -/
inductive FlowSegment where
  | containerVaporToValve
  | valveToHeater
  | heaterToOutlet
  deriving DecidableEq, Fintype, Repr

/-- Nodes joined by the three displayed flow segments. -/
inductive FlowNode where
  | containerVapor
  | valve
  | heater
  | outlet
  deriving DecidableEq, Fintype, Repr

/-- Expected initial node of each left-to-right segment. -/
def expectedSegmentStart : FlowSegment → FlowNode
  | .containerVaporToValve => .containerVapor
  | .valveToHeater => .valve
  | .heaterToOutlet => .heater

/-- Expected final node of each left-to-right segment. -/
def expectedSegmentFinish : FlowSegment → FlowNode
  | .containerVaporToValve => .valve
  | .valveToHeater => .heater
  | .heaterToOutlet => .outlet

/-!
Qualitative content of the primary image. It records phase-region placement,
objects, text, and directed connectivity but contains no numerical flow rate.
-/
structure NitrogenHeaterFigure where
  regionShown : ContainerRegion → Bool
  objectShown : FigureObject → Bool
  textLabelShown : FigureTextLabel → Bool
  liquidRegionBelowVaporRegion : Bool
  containerLeftOfValve : Bool
  valveLeftOfHeater : Bool
  heaterLeftOfOutlet : Bool
  segmentShown : FlowSegment → Bool
  segmentStart : FlowSegment → FlowNode
  segmentFinish : FlowSegment → FlowNode

/-- The liquid state in the constant-cross-section container. -/
structure LiquidNitrogenState where
  phase : MatterPhase
  absoluteTemperature : Temperature
  specificVolume : SpecificVolumeQuantity

/-- The nitrogen-gas state immediately after the heater. -/
structure OutletNitrogenState where
  phase : MatterPhase
  pressure : DimPressure
  absoluteTemperature : Temperature
  specificVolume : SpecificVolumeQuantity

/-!
An external nitrogen property table. The liquid entry is indexed by
temperature, while the gas entry is indexed by pressure and temperature.
-/
structure NitrogenPropertyTable where
  liquidSpecificVolumeAt : Temperature → SpecificVolumeQuantity
  gasSpecificVolumeAt : DimPressure → Temperature → SpecificVolumeQuantity

/-!
Independent physical observables of the experiment. In particular, the
outlet volume-flow rate is an independent dimensionful field; it is not
defined from an answer choice or from the requested numerical value.
-/
structure NitrogenEvaporationSetup where
  workingSubstance : WorkingSubstance
  liquidState : LiquidNitrogenState
  outletState : OutletNitrogenState
  temperatureStorageUnit : TemperatureUnit
  containerCrossSectionalArea : DimArea
  observedLiquidLevelDrop : LengthQuantity
  observationDuration : TimeQuantity
  evaporatedMassFlowRate : MassFlowRateQuantity
  outletMassFlowRate : MassFlowRateQuantity
  outletVolumeFlowRate : VolumeFlowRateQuantity
  levelDropCause : LevelDropCause
  containerCrossSectionIsConstant : Bool
  vaporLeavesContainer : Bool
  flowPassesThroughValve : Bool
  flowPassesThroughHeater : Bool
  propertyTable : NitrogenPropertyTable
  figure : NitrogenHeaterFigure

/-! ## Scenario, figure, property data, and governing laws -/

/-- Qualitative facts stated by the prose scenario. -/
structure MatchesNitrogenEvaporationScenario
    (setup : NitrogenEvaporationSetup) : Prop where
  substanceIsNitrogen : setup.workingSubstance = .nitrogen
  containerContentsAreLiquid : setup.liquidState.phase = .liquid
  outletContentsAreGas : setup.outletState.phase = .gas
  levelFallsByEvaporation :
    setup.levelDropCause = .evaporationDueToHeatTransfer
  constantContainerCrossSection :
    setup.containerCrossSectionIsConstant = true
  vaporExitsContainer : setup.vaporLeavesContainer = true
  vaporTraversesValve : setup.flowPassesThroughValve = true
  vaporTraversesHeater : setup.flowPassesThroughHeater = true

/-- Exact qualitative transcription of the supplied raster. -/
structure MatchesSuppliedNitrogenHeaterFigure
    (figure : NitrogenHeaterFigure) : Prop where
  everyContainerRegionShown : ∀ region, figure.regionShown region = true
  everyObjectShown : ∀ object, figure.objectShown object = true
  everyTextLabelShown : ∀ label, figure.textLabelShown label = true
  liquidIsBelowVapor : figure.liquidRegionBelowVaporRegion = true
  containerPrecedesValve : figure.containerLeftOfValve = true
  valvePrecedesHeater : figure.valveLeftOfHeater = true
  heaterPrecedesOutlet : figure.heaterLeftOfOutlet = true
  everyFlowSegmentShown : ∀ segment, figure.segmentShown segment = true
  displayedSegmentStarts : ∀ segment,
    figure.segmentStart segment = expectedSegmentStart segment
  displayedSegmentFinishes : ∀ segment,
    figure.segmentFinish segment = expectedSegmentFinish segment

/-!
Numerical quantities stated in the prose. There is deliberately no numerical
readout for the requested outlet volume-flow rate in this structure.
-/
structure MatchesProblemReadouts (setup : NitrogenEvaporationSetup) : Prop where
  temperatureUnitIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  liquidTemperatureKelvins :
    temperatureInKelvins setup.temperatureStorageUnit
      setup.liquidState.absoluteTemperature = 100
  containerAreaSquareMeters :
    areaReadout LengthUnit.meters setup.containerCrossSectionalArea = 1 / 2
  levelDropMillimeters :
    lengthReadout LengthUnit.millimeters
      setup.observedLiquidLevelDrop = 30
  observationDurationHours :
    timeReadout TimeUnit.hours setup.observationDuration = 1
  outletPressureKilopascals :
    pressureInKilopascals setup.outletState.pressure = 500
  outletTemperatureKelvins :
    temperatureInKelvins setup.temperatureStorageUnit
      setup.outletState.absoluteTemperature = 260

/-!
Constitutive interpretation of the two states: their independent specific
volumes are supplied by the nitrogen property table at the measured states.
-/
structure SatisfiesNitrogenPropertyModel
    (setup : NitrogenEvaporationSetup) : Prop where
  liquidSpecificVolumeFromTable :
    setup.liquidState.specificVolume =
      setup.propertyTable.liquidSpecificVolumeAt
        setup.liquidState.absoluteTemperature
  outletSpecificVolumeFromTable :
    setup.outletState.specificVolume =
      setup.propertyTable.gasSpecificVolumeAt
        setup.outletState.pressure setup.outletState.absoluteTemperature

/-!
Reference nitrogen property readouts needed to make the numerical exercise
determinate. They are state-property data, not the requested volume-flow rate.
-/
structure MatchesReferenceNitrogenPropertyData
    (setup : NitrogenEvaporationSetup) : Prop where
  liquidSpecificVolumeCubicMetersPerKilogram :
    specificVolumeInCubicMetersPerKilogram
      (setup.propertyTable.liquidSpecificVolumeAt
        setup.liquidState.absoluteTemperature) = 363 / 250000
  outletSpecificVolumeCubicMetersPerKilogram :
    specificVolumeInCubicMetersPerKilogram
      (setup.propertyTable.gasSpecificVolumeAt
        setup.outletState.pressure setup.outletState.absoluteTemperature) =
      1467 / 10000

/-- Positivity conditions selecting the physically meaningful branch. -/
structure HasPhysicalNitrogenFlowParameters
    (setup : NitrogenEvaporationSetup) : Prop where
  areaPositive :
    0 < areaReadout LengthUnit.meters setup.containerCrossSectionalArea
  levelDropPositive :
    0 < lengthReadout LengthUnit.meters setup.observedLiquidLevelDrop
  durationPositive :
    0 < timeReadout TimeUnit.minutes setup.observationDuration
  liquidSpecificVolumePositive :
    0 < specificVolumeInCubicMetersPerKilogram
      setup.liquidState.specificVolume
  outletSpecificVolumePositive :
    0 < specificVolumeInCubicMetersPerKilogram
      setup.outletState.specificVolume
  outletPressurePositive :
    0 < pressureInPascals setup.outletState.pressure
  liquidTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      setup.liquidState.absoluteTemperature
  outletTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      setup.outletState.absoluteTemperature

/-!
The governing flow relations in arbitrary coherent choices of length, mass,
and time units:

* `A Δh = m_dot Δt v_liquid` converts liquid volume loss into evaporated mass;
* mass flow is conserved through the valve and heater; and
* `V_dot_exit = m_dot_exit v_exit` converts outlet mass flow to gas volume flow.

These general laws contain no answer-choice value and no specialized numerical
outlet flow rate.
-/
structure SatisfiesEvaporationAndSteadyFlowLaws
    (setup : NitrogenEvaporationSetup) : Prop where
  liquidVolumeLossDeterminesEvaporatedMass :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      areaReadout lengthUnit setup.containerCrossSectionalArea *
          lengthReadout lengthUnit setup.observedLiquidLevelDrop =
        massFlowRateReadout massUnit timeUnit
            setup.evaporatedMassFlowRate *
          timeReadout timeUnit setup.observationDuration *
          specificVolumeReadout massUnit lengthUnit
            setup.liquidState.specificVolume
  massConservedThroughValveAndHeater :
    ∀ (massUnit : MassUnit) (timeUnit : TimeUnit),
      massFlowRateReadout massUnit timeUnit setup.outletMassFlowRate =
        massFlowRateReadout massUnit timeUnit setup.evaporatedMassFlowRate
  outletGasVolumeFlowLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      volumeFlowRateReadout lengthUnit timeUnit
          setup.outletVolumeFlowRate =
        massFlowRateReadout massUnit timeUnit setup.outletMassFlowRate *
          specificVolumeReadout massUnit lengthUnit
            setup.outletState.specificVolume

/-! ## Answer metadata and current target -/

/-- Labels printed beside the four candidate flow-rate values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Candidate outlet volume flows, reconstructed as cubic metres per minute. -/
def displayedOutletFlowInCubicMetersPerMinute : AnswerChoice → ℝ
  | .A => 352 / 100000
  | .B => 4530 / 100000
  | .C => 1500 / 100000
  | .D => 2526 / 100000

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement at the five decimal places displayed by the answer list. -/
def IsReportedOutletFlowChoice
    (setup : NitrogenEvaporationSetup) (choice : AnswerChoice) : Prop :=
  round
      (100000 * volumeFlowInCubicMetersPerMinute
        setup.outletVolumeFlowRate) =
    round
      (100000 * displayedOutletFlowInCubicMetersPerMinute choice)

/-!
The liquid-volume loss is `(0.5)(0.03) = 0.015 m³` per hour. With the two
reference specific volumes, the resulting outlet volume flow is

`(0.015 / 60) (0.1467 / 0.001452) = 489 / 19360 m³/min`

or `0.025258264... m³/min`. Rounded to the five displayed decimal places this
is `0.02526 m³/min`, uniquely choice D.

Blueprint label: `thm:physics:phyx_mini_0445:target`.
-/
theorem outlet_nitrogen_volume_flow_rate
    (setup : NitrogenEvaporationSetup)
    (_scenario : MatchesNitrogenEvaporationScenario setup)
    (_figure : MatchesSuppliedNitrogenHeaterFigure setup.figure)
    (_readouts : MatchesProblemReadouts setup)
    (_propertyModel : SatisfiesNitrogenPropertyModel setup)
    (_propertyData : MatchesReferenceNitrogenPropertyData setup)
    (_physical : HasPhysicalNitrogenFlowParameters setup)
    (_laws : SatisfiesEvaporationAndSteadyFlowLaws setup) :
    volumeFlowInCubicMetersPerMinute setup.outletVolumeFlowRate =
        489 / 19360 ∧
      IsReportedOutletFlowChoice setup .D ∧
      ∀ choice : AnswerChoice,
        IsReportedOutletFlowChoice setup choice → choice = .D := by
  have hLevelMeters :
      lengthReadout LengthUnit.meters setup.observedLiquidLevelDrop =
        3 / 100 := by
    rw [lengthInMeters_eq_millimeters_div_thousand,
      _readouts.levelDropMillimeters]
    norm_num
  have hDurationMinutes :
      timeReadout TimeUnit.minutes setup.observationDuration = 60 := by
    rw [timeInMinutes_eq_sixty_mul_hours,
      _readouts.observationDurationHours]
    norm_num
  have hLiquidSpecificVolume :
      specificVolumeInCubicMetersPerKilogram
          setup.liquidState.specificVolume =
        363 / 250000 := by
    rw [_propertyModel.liquidSpecificVolumeFromTable]
    exact _propertyData.liquidSpecificVolumeCubicMetersPerKilogram
  change specificVolumeReadout MassUnit.kilograms LengthUnit.meters
    setup.liquidState.specificVolume =
      363 / 250000 at hLiquidSpecificVolume
  have hOutletSpecificVolume :
      specificVolumeInCubicMetersPerKilogram
          setup.outletState.specificVolume =
        1467 / 10000 := by
    rw [_propertyModel.outletSpecificVolumeFromTable]
    exact _propertyData.outletSpecificVolumeCubicMetersPerKilogram
  change specificVolumeReadout MassUnit.kilograms LengthUnit.meters
    setup.outletState.specificVolume =
      1467 / 10000 at hOutletSpecificVolume
  have hLoss := _laws.liquidVolumeLossDeterminesEvaporatedMass
    MassUnit.kilograms LengthUnit.meters TimeUnit.minutes
  have hMass := _laws.massConservedThroughValveAndHeater
    MassUnit.kilograms TimeUnit.minutes
  have hFlow := _laws.outletGasVolumeFlowLaw
    MassUnit.kilograms LengthUnit.meters TimeUnit.minutes
  rw [_readouts.containerAreaSquareMeters, hLevelMeters, hDurationMinutes,
    hLiquidSpecificVolume] at hLoss
  rw [hMass, hOutletSpecificVolume] at hFlow
  have hExact :
      volumeFlowInCubicMetersPerMinute setup.outletVolumeFlowRate =
        489 / 19360 := by
    change volumeFlowRateReadout LengthUnit.meters TimeUnit.minutes
        setup.outletVolumeFlowRate =
      489 / 19360
    norm_num at hLoss hFlow ⊢
    linarith
  refine ⟨hExact, ?_, ?_⟩
  · unfold IsReportedOutletFlowChoice
    rw [hExact]
    norm_num [displayedOutletFlowInCubicMetersPerMinute]
  · intro choice hChoice
    cases choice <;>
      simp_all [IsReportedOutletFlowChoice,
        displayedOutletFlowInCubicMetersPerMinute] <;>
      norm_num [round_eq_iff] at hChoice

end PhyXMiniProblems.ProblemPhyXMini0445
