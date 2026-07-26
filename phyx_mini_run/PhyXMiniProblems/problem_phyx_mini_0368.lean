import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0368

open Dimension

/-!
# Temperature at state 4 of a nitrogen-gas pressure--volume diagram

The primary raster depicts four equilibrium states and two directed processes
from state 1 to state 2:

* `1 -> 3 -> 2`, and
* `1 -> 4 -> 2`.

The plotted coordinates, in `(volume, pressure)` order, are

* state 1: `(100 cm^3, p_1)`;
* state 2: `(100 cm^3, 2 p_1)`;
* state 3: `(50 cm^3, 1.5 p_1)`; and
* state 4: `(150 cm^3, 1.5 p_1)`.

Pressure, volume, mass, and absolute temperature remain physical quantities.
Real numbers occur only as calibrated unit readouts, dimensionless pressure
ratios, figure coordinates, and displayed multiple-choice values.
-/

/-! ## Physical quantities and named-unit readouts -/

/-- A nonnegative physical gas volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass with the mass dimension. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-!
Physlib currently has no amount-of-substance base dimension.  This interface
keeps amount of substance abstract and exposes only its calibrated mole
readout.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in the cubic-centimetre unit printed on the axis. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- Read a dimensionful pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical mass in coherent SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical mass in grams, the unit used in the problem statement. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-! ## State, route, and primary-figure vocabulary -/

/-- The four equilibrium states labelled `1`, `2`, `3`, and `4`. -/
inductive ThermodynamicPoint where
  | state1
  | state2
  | state3
  | state4
  deriving DecidableEq, Fintype, Repr

/-- The four directed straight segments visible in the primary raster. -/
inductive ProcessLeg where
  | state1To3
  | state3To2
  | state1To4
  | state4To2
  deriving DecidableEq, Fintype, Repr

/-- The two alternative processes from state 1 to state 2. -/
inductive ProcessRoute where
  | viaState3
  | viaState4
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed segment. -/
def legStart : ProcessLeg → ThermodynamicPoint
  | .state1To3 => .state1
  | .state3To2 => .state3
  | .state1To4 => .state1
  | .state4To2 => .state4

/-- Final state of a directed segment. -/
def legFinish : ProcessLeg → ThermodynamicPoint
  | .state1To3 => .state3
  | .state3To2 => .state2
  | .state1To4 => .state4
  | .state4To2 => .state2

/-- Ordered segments forming each complete route from state 1 to state 2. -/
def routeLegs : ProcessRoute → List ProcessLeg
  | .viaState3 => [.state1To3, .state3To2]
  | .viaState4 => [.state1To4, .state4To2]

/-- Direction of a straight segment as drawn in the pressure--volume plane. -/
inductive SegmentDirection where
  | upLeft
  | upRight
  deriving DecidableEq, Repr

/-- Direction shown for each of the four arrows in the raster. -/
def displayedSegmentDirection : ProcessLeg → SegmentDirection
  | .state1To3 => .upLeft
  | .state3To2 => .upRight
  | .state1To4 => .upRight
  | .state4To2 => .upLeft

/-- Physical quantities represented by the two plot axes. -/
inductive DiagramAxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Horizontal or vertical plot axis. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Units in which the primary figure's coordinates are transcribed. -/
inductive DiagramCoordinateUnit where
  | cubicCentimeter
  | multipleOfP1
  deriving DecidableEq, Repr

/-- Equation-of-state model assigned to the nitrogen sample. -/
inductive GasModel where
  | idealGas
  | other
  deriving DecidableEq, Repr

/-- Working-gas species named in the question. -/
inductive GasSpecies where
  | nitrogen
  | other
  deriving DecidableEq, Repr

/-- Physical observables at one labelled equilibrium state. -/
structure ThermodynamicStateData where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
Literal and coordinate information transcribed from the supplied image.
Pressure coordinates are dimensionless multiples of the plotted reference
pressure `p_1`; volume coordinates are cubic-centimetre readouts.
-/
structure PressureVolumeDiagram where
  axisQuantity : DiagramAxis → DiagramAxisQuantity
  axisUnit : DiagramAxis → DiagramCoordinateUnit
  axisMinimum : DiagramAxis → ℝ
  axisMaximum : DiagramAxis → ℝ
  pointLabel : ThermodynamicPoint → String
  showsPoint : ThermodynamicPoint → Bool
  pointVolumeCubicCentimeters : ThermodynamicPoint → ℝ
  pointPressureMultipleOfP1 : ThermodynamicPoint → ℝ
  showsDirectedArrow : ProcessLeg → Bool
  arrowStart : ProcessLeg → ThermodynamicPoint
  arrowFinish : ProcessLeg → ThermodynamicPoint
  segmentIsStraight : ProcessLeg → Bool
  segmentDirection : ProcessLeg → SegmentDirection

/-!
Independent data for the fixed 1.0 g nitrogen sample.  The amount of gas is a
single physical quantity shared by all four states.  Neither state 4's
temperature nor a selected answer is stored as a field.
-/
structure NitrogenGasDiagramSetup (amountScale : AmountOfSubstanceScale) where
  species : GasSpecies
  gasModel : GasModel
  sampleMass : MassQuantity
  gasAmount : amountScale.Quantity
  nitrogenMolarMassGramsPerMole : ℝ
  universalGasConstantJoulesPerMoleKelvin : ℝ
  temperatureStorageUnit : TemperatureUnit
  referencePressureP1 : DimPressure
  stateAt : ThermodynamicPoint → ThermodynamicStateData
  figure : PressureVolumeDiagram

/-- Mole readout of the amount of nitrogen in the fixed sample. -/
def gasAmountInMoles
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale) : ℝ :=
  amountScale.inMoles setup.gasAmount

/-- Kelvin readout of a state's absolute temperature. -/
def temperatureInKelvins
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale)
    (point : ThermodynamicPoint) : ℝ :=
  let unitRatio : NNReal :=
    setup.temperatureStorageUnit / TemperatureUnit.kelvin
  (setup.stateAt point).temperature.toReal * (unitRatio : ℝ)

/-- Degree-Celsius readout, using the exact offset `273.15 K`. -/
def temperatureInDegreesCelsius
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale)
    (point : ThermodynamicPoint) : ℝ :=
  temperatureInKelvins setup point - (5463 / 20 : ℝ)

/-- Pressure at a state as a dimensionless multiple of the reference `p_1`. -/
def pressureMultipleOfP1
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale)
    (point : ThermodynamicPoint) : ℝ :=
  pressureInPascals (setup.stateAt point).pressure /
    pressureInPascals setup.referencePressureP1

/-! ## Scenario, figure/data readouts, and governing laws -/

/-- Qualitative scenario data, including the selected absolute-temperature unit. -/
structure MatchesNitrogenGasScenario
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale) : Prop where
  speciesIsNitrogen : setup.species = .nitrogen
  modelIsIdealGas : setup.gasModel = .idealGas
  temperatureUnitIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  referencePressureIsState1Pressure :
    setup.referencePressureP1 = (setup.stateAt .state1).pressure

/-- Numerical readouts stated in the prose, with no state-4 temperature data. -/
structure MatchesProblemReadouts
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale) : Prop where
  sampleMassIsOneGram : massInGrams setup.sampleMass = 1
  state1TemperatureIs25Celsius :
    temperatureInDegreesCelsius setup .state1 = 25

/-!
All information read directly from the primary raster.  In particular, the
figure shows two directed routes from state 1 to state 2, not the directed
four-leg cycle described by the auxiliary caption.
-/
structure MatchesSuppliedPressureVolumeDiagram
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  horizontalAxisUsesCubicCentimeters :
    setup.figure.axisUnit .horizontal = .cubicCentimeter
  horizontalAxisRange :
    setup.figure.axisMinimum .horizontal = 0 ∧
      setup.figure.axisMaximum .horizontal = 150
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  verticalAxisUsesMultiplesOfP1 :
    setup.figure.axisUnit .vertical = .multipleOfP1
  verticalAxisRange :
    setup.figure.axisMinimum .vertical = 0 ∧
      setup.figure.axisMaximum .vertical = 2
  allPointLabelsShown :
    setup.figure.pointLabel .state1 = "1" ∧
      setup.figure.pointLabel .state2 = "2" ∧
      setup.figure.pointLabel .state3 = "3" ∧
      setup.figure.pointLabel .state4 = "4" ∧
      ∀ point, setup.figure.showsPoint point = true
  state1Coordinate :
    setup.figure.pointVolumeCubicCentimeters .state1 = 100 ∧
      setup.figure.pointPressureMultipleOfP1 .state1 = 1
  state2Coordinate :
    setup.figure.pointVolumeCubicCentimeters .state2 = 100 ∧
      setup.figure.pointPressureMultipleOfP1 .state2 = 2
  state3Coordinate :
    setup.figure.pointVolumeCubicCentimeters .state3 = 50 ∧
      setup.figure.pointPressureMultipleOfP1 .state3 = (3 / 2 : ℝ)
  state4Coordinate :
    setup.figure.pointVolumeCubicCentimeters .state4 = 150 ∧
      setup.figure.pointPressureMultipleOfP1 .state4 = (3 / 2 : ℝ)
  coordinatesRepresentPhysicalStates :
    ∀ point,
      setup.figure.pointVolumeCubicCentimeters point =
          volumeInCubicCentimeters (setup.stateAt point).volume ∧
        setup.figure.pointPressureMultipleOfP1 point =
          pressureMultipleOfP1 setup point
  everyDirectedArrowShown :
    ∀ leg, setup.figure.showsDirectedArrow leg = true
  directedArrowEndpoints :
    ∀ leg,
      setup.figure.arrowStart leg = legStart leg ∧
        setup.figure.arrowFinish leg = legFinish leg
  everySegmentStraight :
    ∀ leg, setup.figure.segmentIsStraight leg = true
  segmentDirectionsAgree :
    ∀ leg,
      setup.figure.segmentDirection leg = displayedSegmentDirection leg

/-- Positivity and nondegeneracy conditions for the physical gas states. -/
structure HasPhysicalParameters
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale) : Prop where
  sampleMassPositive : 0 < massInGrams setup.sampleMass
  gasAmountPositive : 0 < gasAmountInMoles setup
  nitrogenMolarMassPositive : 0 < setup.nitrogenMolarMassGramsPerMole
  universalGasConstantPositive :
    0 < setup.universalGasConstantJoulesPerMoleKelvin
  referencePressurePositive :
    0 < pressureInPascals setup.referencePressureP1
  statePressurePositive :
    ∀ point, 0 < pressureInPascals (setup.stateAt point).pressure
  stateVolumePositive :
    ∀ point, 0 < volumeInCubicMeters (setup.stateAt point).volume
  absoluteTemperaturePositive :
    ∀ point, 0 < temperatureInKelvins setup point

/-!
General physical laws used in the calculation.  The mass--amount relation
identifies the amount of the 1.0 g nitrogen sample, while `p V = n R T` is
imposed uniformly at every equilibrium state.  Neither law contains the
requested temperature or any answer-choice value.
-/
structure SatisfiesIdealNitrogenGasLaws
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale) : Prop where
  massAmountConsistency :
    massInGrams setup.sampleMass =
      gasAmountInMoles setup * setup.nitrogenMolarMassGramsPerMole
  idealGasEquation :
    ∀ point,
      pressureInPascals (setup.stateAt point).pressure *
          volumeInCubicMeters (setup.stateAt point).volume =
        gasAmountInMoles setup *
          setup.universalGasConstantJoulesPerMoleKelvin *
            temperatureInKelvins setup point

/-! ## Exact state-4 temperature and displayed answer -/

/-- The four answer letters printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Whole-degree Celsius temperature printed beside each answer letter. -/
def displayedTemperatureDegreesCelsius : AnswerChoice → ℝ
  | .A => 398
  | .B => 556
  | .C => 636
  | .D => 784

/-- Dataset metadata recording the supplied answer label. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- The computed state-4 temperature rounds to a displayed whole degree. -/
def RoundsToDisplayedWholeDegree
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale)
    (choice : AnswerChoice) : Prop :=
  |temperatureInDegreesCelsius setup .state4 -
      displayedTemperatureDegreesCelsius choice| < (1 / 2 : ℝ)

/-- The selected displayed value is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedTemperature
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |temperatureInDegreesCelsius setup .state4 -
        displayedTemperatureDegreesCelsius choice| <
      |temperatureInDegreesCelsius setup .state4 -
        displayedTemperatureDegreesCelsius other|

/-!
The state-4 pressure--volume product is `9/4` of the state-1 product.
Since the amount and gas constant are common to all states, the ideal-gas law
gives `T_4 = (9/4) T_1 = 53667/80 K = 670.8375 K`.
-/
lemma state4_temperature_in_kelvins_exact
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale)
    (hScenario : MatchesNitrogenGasScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedPressureVolumeDiagram setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesIdealNitrogenGasLaws setup) :
    temperatureInKelvins setup .state4 = (53667 / 80 : ℝ) := by
  have hT1 :
      temperatureInKelvins setup .state1 = (5963 / 20 : ℝ) := by
    have h := hReadouts.state1TemperatureIs25Celsius
    unfold temperatureInDegreesCelsius at h
    norm_num at h ⊢
    linarith
  have hV1 :
      volumeInCubicCentimeters (setup.stateAt .state1).volume = 100 := by
    rw [← (hFigure.coordinatesRepresentPhysicalStates .state1).1]
    exact hFigure.state1Coordinate.1
  have hV4 :
      volumeInCubicCentimeters (setup.stateAt .state4).volume = 150 := by
    rw [← (hFigure.coordinatesRepresentPhysicalStates .state4).1]
    exact hFigure.state4Coordinate.1
  have hVolumeRatio :
      volumeInCubicMeters (setup.stateAt .state4).volume =
        (3 / 2 : ℝ) *
          volumeInCubicMeters (setup.stateAt .state1).volume := by
    unfold volumeInCubicCentimeters at hV1 hV4
    linarith
  have hP4 :
      pressureMultipleOfP1 setup .state4 = (3 / 2 : ℝ) := by
    rw [← (hFigure.coordinatesRepresentPhysicalStates .state4).2]
    exact hFigure.state4Coordinate.2
  unfold pressureMultipleOfP1 at hP4
  have hReferencePressureNe :
      pressureInPascals setup.referencePressureP1 ≠ 0 :=
    ne_of_gt hPhysical.referencePressurePositive
  have hPressureRatio :
      pressureInPascals (setup.stateAt .state4).pressure =
        (3 / 2 : ℝ) *
          pressureInPascals (setup.stateAt .state1).pressure := by
    have h := (div_eq_iff hReferencePressureNe).mp hP4
    rw [hScenario.referencePressureIsState1Pressure] at h
    exact h
  have hLaw1 := hLaws.idealGasEquation .state1
  have hLaw4 := hLaws.idealGasEquation .state4
  rw [hT1] at hLaw1
  rw [hPressureRatio, hVolumeRatio] at hLaw4
  have hAmountTimesConstantPositive :
      0 < gasAmountInMoles setup *
        setup.universalGasConstantJoulesPerMoleKelvin :=
    mul_pos hPhysical.gasAmountPositive
      hPhysical.universalGasConstantPositive
  nlinarith [hLaw1, hLaw4, hAmountTimesConstantPositive]

/-!
Thus state 4 is exactly `6363/16 degrees Celsius = 397.6875 degrees Celsius`.
It rounds to `398 degrees Celsius`, answer A, and is strictly closer to A than
to any of the other displayed temperatures.
-/
theorem problem_phyx_mini_0368
    {amountScale : AmountOfSubstanceScale}
    (setup : NitrogenGasDiagramSetup amountScale)
    (hScenario : MatchesNitrogenGasScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedPressureVolumeDiagram setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesIdealNitrogenGasLaws setup) :
    temperatureInDegreesCelsius setup .state4 = (6363 / 16 : ℝ) ∧
      RoundsToDisplayedWholeDegree setup .A ∧
      IsUniqueClosestDisplayedTemperature setup .A := by
  have hT4K :=
    state4_temperature_in_kelvins_exact setup hScenario hReadouts hFigure
      hPhysical hLaws
  have hT4C :
      temperatureInDegreesCelsius setup .state4 = (6363 / 16 : ℝ) := by
    unfold temperatureInDegreesCelsius
    rw [hT4K]
    norm_num
  refine ⟨hT4C, ?_, ?_⟩
  · unfold RoundsToDisplayedWholeDegree
    rw [hT4C]
    norm_num [displayedTemperatureDegreesCelsius]
  · unfold IsUniqueClosestDisplayedTemperature
    intro other hOther
    rw [hT4C]
    cases other with
    | A => contradiction
    | B => norm_num [displayedTemperatureDegreesCelsius]
    | C => norm_num [displayedTemperatureDegreesCelsius]
    | D => norm_num [displayedTemperatureDegreesCelsius]

end PhyXMiniProblems.ProblemPhyXMini0368
