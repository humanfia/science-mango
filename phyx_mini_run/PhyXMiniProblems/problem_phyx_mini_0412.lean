import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Heat in an isochoric cooling of a monatomic ideal gas

This file formalizes problem `phyx_mini_0412`.  The supplied pressure-volume
diagram shows a monatomic gas following the path `1 → 2 → 3`.  Its plotted
coordinates are

* state `1`: `p = 3 atm`, `V = 100 cm³`;
* state `2`: `p = 3 atm`, `V = 300 cm³`;
* state `3`: `p = 1 atm`, `V = 300 cm³`.

The leg `1 → 2` is an isobaric expansion and `2 → 3` is an isochoric cooling.
A dashed red `100°C isotherm` passes through states `1` and `3`, but is not a
path traversed by the gas.

Pressure, volume, absolute temperature, heat, work, and internal energy remain
dimensionful physical quantities.  Real numbers occur only as explicitly
unit-labelled readouts, conversion factors, and displayed answer values.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the prose and bitmap readouts;
* `HasPhysicalStateCoordinates` records positivity of the states;
* `ObeysMonatomicIdealGasThermodynamics` states the monatomic internal-energy
  relation, the first law, and zero boundary work for an isochoric leg; and
* `heatForTwoToThree_matches_recordedAnswerC` derives the requested heat.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0412

open Dimension

/-! ## Dimensionful thermodynamic quantities and named unit readouts -/

/-- A nonnegative physical volume, carrying dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Thermodynamic pressure, represented by Physlib's dimensionful pressure type. -/
abbrev PressureQuantity : Type := DimPressure

/-- A nonnegative absolute temperature, carrying the temperature dimension. -/
abbrev TemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-- Signed heat, work, or internal energy, represented by dimensionful energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used by the horizontal axis of the figure. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Standard-atmosphere readout used by the vertical axis of the figure. -/
def pressureInStandardAtmospheres (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

/-- SI kelvin readout of an absolute temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  ((temperature UnitChoices.SI).val : ℝ)

/-- Degrees-Celsius readout used by the dashed isotherm annotation. -/
def temperatureInDegreesCelsius (temperature : TemperatureQuantity) : ℝ :=
  temperatureInKelvins temperature - 27315 / 100

/-- Joule readout of a signed dimensionful energy quantity. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-!
One standard atmosphere times one cubic centimetre, expressed in joules.
This is the unit conversion `101325 Pa × 10⁻⁶ m³ = 0.101325 J`.
-/
def atmosphereCubicCentimeterInJoules : ℝ :=
  101325 / 10 ^ 6

/-! ## Gas, state, process, and primary-figure vocabulary -/

/-- Atomicity of the gas specified by the problem. -/
inductive GasAtomicity where
  | monatomic
  deriving DecidableEq, Repr

/-- Equation-of-state model used for the gas. -/
inductive GasModel where
  | ideal
  deriving DecidableEq, Repr

/-- A physical gas sample, distinguished from any of its scalar readouts. -/
structure GasSample where
  atomicity : GasAtomicity
  model : GasModel

/-- The three state labels printed in the pressure-volume diagram. -/
inductive StateLabel where
  | state1
  | state2
  | state3
  deriving DecidableEq, Repr

/-- The two directed process legs followed by the gas. -/
inductive ProcessLeg where
  | oneToTwo
  | twoToThree
  deriving DecidableEq, Repr

/-- Thermodynamic classification of a depicted process leg. -/
inductive ProcessKind where
  | isobaric
  | isochoric
  deriving DecidableEq, Repr

/-- Qualitative change indicated by a directed process arrow. -/
inductive ProcessDirection where
  | expansion
  | cooling
  deriving DecidableEq, Repr

/-- Pressure, volume, temperature, and internal energy at equilibrium. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  absoluteTemperature : TemperatureQuantity
  internalEnergy : EnergyQuantity

/-!
A directed thermodynamic process.  Heat is positive when transferred into the
gas, and boundary work is positive when done by the gas.  Neither energy field
is defined from an answer choice.
-/
structure ThermodynamicProcess where
  initialState : StateLabel
  finalState : StateLabel
  kind : ProcessKind
  direction : ProcessDirection
  heatTransferredToGas : EnergyQuantity
  boundaryWorkDoneByGas : EnergyQuantity

/-- The two Cartesian axes in the primary pressure-volume diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical role assigned to a figure axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside a figure axis. -/
inductive AxisDisplayUnit where
  | cubicCentimeters
  | standardAtmospheres
  deriving DecidableEq, Repr

/-- Literal physical-quantity symbol printed beside a figure axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Geometric appearance of a process leg in the `p`-`V` plane. -/
inductive PathGeometry where
  | horizontalStraightSegment
  | verticalStraightSegment
  deriving DecidableEq, Repr

/-- Visible line style used for a feature of the diagram. -/
inductive FigureLineStyle where
  | solidBlack
  | dashedRed
  deriving DecidableEq, Repr

/-!
Structured transcription of image `412.png`.  The dashed isotherm is retained
as a figure feature separate from the two solid paths actually followed.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  stateLabelVisible : StateLabel → Bool
  plottedPressure : StateLabel → PressureQuantity
  plottedVolume : StateLabel → VolumeQuantity
  pathStart : ProcessLeg → StateLabel
  pathFinish : ProcessLeg → StateLabel
  pathGeometry : ProcessLeg → PathGeometry
  pathLineStyle : ProcessLeg → FigureLineStyle
  directionArrowShown : ProcessLeg → Bool
  isothermLineStyle : FigureLineStyle
  isothermStart : StateLabel
  isothermFinish : StateLabel
  isothermTemperatureCelsius : ℝ
  isothermIsTraversedByGas : Bool

/-- The gas, its three states, the two process legs, and the supplied figure. -/
structure MonatomicGasProcessSetup where
  gas : GasSample
  state : StateLabel → ThermodynamicState
  process : ProcessLeg → ThermodynamicProcess
  figure : PressureVolumeFigure

/-! ## Problem statement and primary-figure readouts -/

/-!
Exact transcription of the prose and primary bitmap.  The figure fixes state
coordinates, process classifications, directions, and the dashed `100°C`
isotherm.  It supplies no numerical heat, work, or internal-energy value.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : MonatomicGasProcessSetup) : Prop where
  gasIsMonatomic : setup.gas.atomicity = .monatomic
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUnitIsCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalAxisUnitIsStandardAtmospheres :
    setup.figure.axisDisplayUnit .vertical = .standardAtmospheres
  horizontalAxisSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalAxisSymbolIsP : setup.figure.axisSymbol .vertical = .p
  allStateLabelsAreVisible :
    ∀ label : StateLabel, setup.figure.stateLabelVisible label = true
  plottedCoordinatesAreGasStates : ∀ label : StateLabel,
    setup.figure.plottedPressure label = (setup.state label).pressure ∧
      setup.figure.plottedVolume label = (setup.state label).volume
  state1PressureAtmospheres :
    pressureInStandardAtmospheres
      (setup.figure.plottedPressure .state1) = 3
  state1VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state1) = 100
  state2PressureAtmospheres :
    pressureInStandardAtmospheres
      (setup.figure.plottedPressure .state2) = 3
  state2VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state2) = 300
  state3PressureAtmospheres :
    pressureInStandardAtmospheres
      (setup.figure.plottedPressure .state3) = 1
  state3VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state3) = 300
  processEndpointsMatchFigure : ∀ leg : ProcessLeg,
    setup.figure.pathStart leg = (setup.process leg).initialState ∧
      setup.figure.pathFinish leg = (setup.process leg).finalState
  oneToTwoEndpoints :
    (setup.process .oneToTwo).initialState = .state1 ∧
      (setup.process .oneToTwo).finalState = .state2
  twoToThreeEndpoints :
    (setup.process .twoToThree).initialState = .state2 ∧
      (setup.process .twoToThree).finalState = .state3
  oneToTwoIsHorizontal :
    setup.figure.pathGeometry .oneToTwo = .horizontalStraightSegment
  twoToThreeIsVertical :
    setup.figure.pathGeometry .twoToThree = .verticalStraightSegment
  bothPathsAreSolidBlack : ∀ leg : ProcessLeg,
    setup.figure.pathLineStyle leg = .solidBlack
  bothDirectionArrowsAreShown : ∀ leg : ProcessLeg,
    setup.figure.directionArrowShown leg = true
  oneToTwoIsIsobaricExpansion :
    (setup.process .oneToTwo).kind = .isobaric ∧
      (setup.process .oneToTwo).direction = .expansion
  twoToThreeIsIsochoricCooling :
    (setup.process .twoToThree).kind = .isochoric ∧
      (setup.process .twoToThree).direction = .cooling
  isothermIsDashedRed : setup.figure.isothermLineStyle = .dashedRed
  isothermRunsFromOneToThree :
    setup.figure.isothermStart = .state1 ∧
      setup.figure.isothermFinish = .state3
  isothermLabelIsOneHundredCelsius :
    setup.figure.isothermTemperatureCelsius = 100
  stateOneAndThreeAreAtOneHundredCelsius :
    temperatureInDegreesCelsius
        (setup.state .state1).absoluteTemperature = 100 ∧
      temperatureInDegreesCelsius
        (setup.state .state3).absoluteTemperature = 100
  dashedIsothermIsNotTraversed :
    setup.figure.isothermIsTraversedByGas = false

/-- Positivity conditions selecting physically meaningful state coordinates. -/
structure HasPhysicalStateCoordinates
    (setup : MonatomicGasProcessSetup) : Prop where
  pressurePositive : ∀ label : StateLabel,
    0 < pressureInPascals (setup.state label).pressure
  volumePositive : ∀ label : StateLabel,
    0 < volumeInCubicMeters (setup.state label).volume
  absoluteTemperaturePositive : ∀ label : StateLabel,
    0 < temperatureInKelvins (setup.state label).absoluteTemperature

/-! ## Governing thermodynamic laws -/

/-!
The laws used for a monatomic ideal gas, with explicit unit readouts:

* `U = (3/2) pV` at each equilibrium state;
* `Q_in = ΔU + W_by` for each directed process; and
* an isochoric leg has zero boundary work.

All three relations are generic over the setup's states or legs and contain no
problem-specific heat value or answer choice.
-/
structure ObeysMonatomicIdealGasThermodynamics
    (setup : MonatomicGasProcessSetup) : Prop where
  gasUsesIdealModel : setup.gas.model = .ideal
  internalEnergyFromPressureVolume : ∀ label : StateLabel,
    energyInJoules (setup.state label).internalEnergy =
      (3 / 2) * atmosphereCubicCentimeterInJoules *
        pressureInStandardAtmospheres (setup.state label).pressure *
          volumeInCubicCentimeters (setup.state label).volume
  firstLawForProcess : ∀ leg : ProcessLeg,
    energyInJoules (setup.process leg).heatTransferredToGas =
      energyInJoules
          (setup.state (setup.process leg).finalState).internalEnergy -
        energyInJoules
          (setup.state (setup.process leg).initialState).internalEnergy +
        energyInJoules (setup.process leg).boundaryWorkDoneByGas
  zeroBoundaryWorkForIsochoricProcess : ∀ leg : ProcessLeg,
    (setup.process leg).kind = .isochoric →
      energyInJoules (setup.process leg).boundaryWorkDoneByGas = 0

/-! ## Answer choices and requested conclusion -/

/-- The four labels printed beside the multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Heat readout in joules printed beside each answer label. -/
def displayedHeatInJoules : AnswerChoice → ℝ
  | .A => 91
  | .B => 0
  | .C => -91
  | .D => -150

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A unit-labelled heat readout rounds to a displayed whole-joule value when it
lies strictly within half a joule of that value.  This generic display rule
contains no problem-specific answer.
-/
def RoundsToNearestWholeJoule
    (heat : EnergyQuantity) (wholeJoules : ℝ) : Prop :=
  |energyInJoules heat - wholeJoules| < 1 / 2

/-!
The governing laws and the state-2/state-3 figure data give

`Q₂₃ = (3/2)(1 atm·300 cm³ - 3 atm·300 cm³)`.

This intermediate heat relation is a conclusion, not a premise field.
-/
lemma heatForTwoToThree_from_monatomic_first_law
    (setup : MonatomicGasProcessSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_laws : ObeysMonatomicIdealGasThermodynamics setup) :
    energyInJoules
        (setup.process .twoToThree).heatTransferredToGas =
      (3 / 2) * atmosphereCubicCentimeterInJoules *
        (1 * 300 - 3 * 300) := by
  have hstate2Pressure :
      pressureInStandardAtmospheres (setup.state .state2).pressure = 3 := by
    rw [← (_problem.plottedCoordinatesAreGasStates .state2).1]
    exact _problem.state2PressureAtmospheres
  have hstate2Volume :
      volumeInCubicCentimeters (setup.state .state2).volume = 300 := by
    rw [← (_problem.plottedCoordinatesAreGasStates .state2).2]
    exact _problem.state2VolumeCubicCentimeters
  have hstate3Pressure :
      pressureInStandardAtmospheres (setup.state .state3).pressure = 1 := by
    rw [← (_problem.plottedCoordinatesAreGasStates .state3).1]
    exact _problem.state3PressureAtmospheres
  have hstate3Volume :
      volumeInCubicCentimeters (setup.state .state3).volume = 300 := by
    rw [← (_problem.plottedCoordinatesAreGasStates .state3).2]
    exact _problem.state3VolumeCubicCentimeters
  rw [_laws.firstLawForProcess .twoToThree,
    _problem.twoToThreeEndpoints.2, _problem.twoToThreeEndpoints.1,
    _laws.internalEnergyFromPressureVolume .state3,
    _laws.internalEnergyFromPressureVolume .state2,
    _laws.zeroBoundaryWorkForIsochoricProcess .twoToThree
      _problem.twoToThreeIsIsochoricCooling.1,
    hstate3Pressure, hstate3Volume, hstate2Pressure, hstate2Volume]
  ring

/-!
Thus the heat transferred into the gas during `2 → 3` is exactly
`-36477/400 J = -91.1925 J`, which rounds to the displayed `-91 J`, answer C.
The negative sign means that heat leaves the gas during the isochoric cooling.

Blueprint label: `thm:physics:phyx_mini_0412:target`.
-/
theorem heatForTwoToThree_matches_recordedAnswerC
    (setup : MonatomicGasProcessSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalStateCoordinates setup)
    (_laws : ObeysMonatomicIdealGasThermodynamics setup) :
    energyInJoules
          (setup.process .twoToThree).heatTransferredToGas =
        -(36477 / 400) ∧
      RoundsToNearestWholeJoule
        (setup.process .twoToThree).heatTransferredToGas
        (displayedHeatInJoules recordedAnswerChoice) := by
  have hheat :
      energyInJoules
          (setup.process .twoToThree).heatTransferredToGas =
        (3 / 2) * atmosphereCubicCentimeterInJoules *
          (1 * 300 - 3 * 300) :=
    heatForTwoToThree_from_monatomic_first_law setup _problem _laws
  have hheatExact :
      energyInJoules
          (setup.process .twoToThree).heatTransferredToGas =
        -(36477 / 400) := by
    calc
      energyInJoules
          (setup.process .twoToThree).heatTransferredToGas =
          (3 / 2) * atmosphereCubicCentimeterInJoules *
            (1 * 300 - 3 * 300) := hheat
      _ = -(36477 / 400) := by
        norm_num [atmosphereCubicCentimeterInJoules]
  refine ⟨hheatExact, ?_⟩
  unfold RoundsToNearestWholeJoule
  rw [hheatExact]
  norm_num [displayedHeatInJoules, recordedAnswerChoice]

end PhyXMiniProblems.ProblemPhyXMini0412
