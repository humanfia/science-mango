import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0367

open Dimension

/-!
# Temperature after an isothermal expansion of helium

The primary `p`--`V` image shows three equilibrium states and the directed
process `1 → 2 → 3`.  The first leg is vertical and hence isochoric;
the second leg is the curved segment explicitly annotated "Isothermal".
This corrects the auxiliary caption's description of the vertical leg as
isobaric.

Mass, pressure, and volume remain dimensionful physical quantities.
Temperatures use Physlib's absolute `Temperature`; real numbers are used only
for calibrated unit readouts and qualitative drawing coordinates.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical mass, of dimension `mass`. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical volume, of dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical mass in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ) * 1000

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-!
Physlib's `Temperature` has an arbitrary absolute scale.  For this problem
that scale is calibrated in kelvin, so `Temperature.toReal` is the kelvin
readout.
-/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  Temperature.toReal temperature

/-- Celsius readout obtained from the calibrated absolute temperature. -/
def temperatureInCelsius (temperature : Temperature) : ℝ :=
  temperatureInKelvin temperature - (27315 / 100 : ℝ)

/-! ## Process states, legs, and figure geometry -/

/-- The three equilibrium states labelled `1`, `2`, and `3` in the image. -/
inductive ProcessState where
  | one
  | two
  | three
  deriving DecidableEq, Repr

/-- The two directed process legs shown by arrows in the image. -/
inductive ProcessLeg where
  | oneToTwo
  | twoToThree
  deriving DecidableEq, Repr

/-- Initial state of a directed process leg. -/
def ProcessLeg.initialState : ProcessLeg → ProcessState
  | .oneToTwo => .one
  | .twoToThree => .two

/-- Final state of a directed process leg. -/
def ProcessLeg.finalState : ProcessLeg → ProcessState
  | .oneToTwo => .two
  | .twoToThree => .three

/-- Thermodynamic character of a process leg. -/
inductive ProcessKind where
  | isochoric
  | isothermal
  deriving DecidableEq, Repr

/-- Working substance named in the scenario. -/
inductive WorkingSubstance where
  | helium
  | other
  deriving DecidableEq, Repr

/-- Horizontal or vertical axis of the supplied diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity assigned to a figure axis. -/
inductive FigureAxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- Qualitative geometric shape of a process segment in the raster. -/
inductive PVSegmentShape where
  | vertical
  | curved
  deriving DecidableEq, Repr

/-- Pressure, volume, and absolute temperature at one equilibrium state. -/
structure ThermodynamicStateData where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
Qualitative evidence retained from the supplied raster.  Coordinates record
only relative placement in the drawing; physical state quantities are stored
separately in `HeliumPVProcessSetup`.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → FigureAxisQuantity
  statePointShown : ProcessState → Bool
  arrowStart : ProcessLeg → ProcessState
  arrowEnd : ProcessLeg → ProcessState
  segmentShape : ProcessLeg → PVSegmentShape
  horizontalCoordinate : ProcessState → ℝ
  verticalCoordinate : ProcessState → ℝ
  isothermalAnnotationShown : Bool

/-!
Independent physical quantities in the scenario, including the labels
`V₁`, `V₃`, and `p₂`.  No field fixes the requested temperature at
state `3`.
-/
structure HeliumPVProcessSetup where
  substance : WorkingSubstance
  gasMass : MassQuantity
  state : ProcessState → ThermodynamicStateData
  volumeV1 : VolumeQuantity
  volumeV3 : VolumeQuantity
  pressureP2 : DimPressure
  processKind : ProcessLeg → ProcessKind
  figure : PressureVolumeFigure

/-! ## Assumptions: physical branch, process laws, and figure readouts -/

/-- Positivity conditions selecting physical pressures, volumes, and temperatures. -/
structure HasPhysicalParameters (setup : HeliumPVProcessSetup) : Prop where
  gasMassPositive : 0 < massInGrams setup.gasMass
  volumeV1Positive : 0 < volumeInCubicMeters setup.volumeV1
  volumeV3Positive : 0 < volumeInCubicMeters setup.volumeV3
  statePressurePositive :
    ∀ state, 0 < pressureInPascals (setup.state state).pressure
  stateTemperaturePositive :
    ∀ state, 0 < temperatureInKelvin (setup.state state).temperature

/-!
Governing semantics of the two named process kinds.  These are general laws:
an isochoric leg preserves physical volume, and an isothermal leg preserves
absolute temperature.  They contain no numerical value for `T₃`.
-/
structure SatisfiesProcessSemantics (setup : HeliumPVProcessSetup) : Prop where
  isochoricPreservesVolume :
    ∀ leg, setup.processKind leg = .isochoric →
      (setup.state leg.initialState).volume =
        (setup.state leg.finalState).volume
  isothermalPreservesTemperature :
    ∀ leg, setup.processKind leg = .isothermal →
      (setup.state leg.initialState).temperature =
        (setup.state leg.finalState).temperature

/-!
Scenario data and direct readouts from the primary image.  In particular,
states `1` and `3` lie at the `2 atm` height, states `1` and `2` lie over
`V₁`, state `3` lies over `V₃`, and the image labels the temperature of
state `2` as `657 °C`.  The requested state-`3` temperature is deliberately
absent.
-/
structure HasScenarioAndFigureData (setup : HeliumPVProcessSetup) : Prop where
  workingSubstanceIsHelium : setup.substance = .helium
  gasMassIsEightGrams : massInGrams setup.gasMass = 8
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  everyStatePointIsShown :
    ∀ state, setup.figure.statePointShown state = true
  arrowsFollowProcessOrder :
    ∀ leg,
      setup.figure.arrowStart leg = leg.initialState ∧
        setup.figure.arrowEnd leg = leg.finalState
  firstLegIsVertical :
    setup.figure.segmentShape .oneToTwo = .vertical
  secondLegIsCurved :
    setup.figure.segmentShape .twoToThree = .curved
  isothermalAnnotationIsShown :
    setup.figure.isothermalAnnotationShown = true
  firstLegIsIsochoric :
    setup.processKind .oneToTwo = .isochoric
  secondLegIsIsothermal :
    setup.processKind .twoToThree = .isothermal
  stateOneAtV1 : (setup.state .one).volume = setup.volumeV1
  stateTwoAtV1 : (setup.state .two).volume = setup.volumeV1
  stateThreeAtV3 : (setup.state .three).volume = setup.volumeV3
  stateTwoAtP2 : (setup.state .two).pressure = setup.pressureP2
  stateOnePressureIsTwoAtmospheres :
    ∀ units,
      ((setup.state .one).pressure units).val =
        2 * (DimPressure.standardAtmosphere units).val
  stateThreePressureIsTwoAtmospheres :
    ∀ units,
      ((setup.state .three).pressure units).val =
        2 * (DimPressure.standardAtmosphere units).val
  stateOneTemperatureIs37Celsius :
    temperatureInCelsius (setup.state .one).temperature = 37
  stateTwoTemperatureIs657Celsius :
    temperatureInCelsius (setup.state .two).temperature = 657
  stateOneAndTwoShareHorizontalCoordinate :
    setup.figure.horizontalCoordinate .one =
      setup.figure.horizontalCoordinate .two
  stateThreeIsRightOfStateTwo :
    setup.figure.horizontalCoordinate .two <
      setup.figure.horizontalCoordinate .three
  stateOneAndThreeShareVerticalCoordinate :
    setup.figure.verticalCoordinate .one =
      setup.figure.verticalCoordinate .three
  stateTwoIsAboveStateOne :
    setup.figure.verticalCoordinate .one <
      setup.figure.verticalCoordinate .two

/-!
The temperature at state `3` is `657 °C` (answer choice A).

The numerical premise concerns state `2`; the isothermal process law must
still be applied to transport that temperature to state `3`.

Blueprint label: `thm:physics:phyx_mini_0367:target`.
-/
theorem temperatureAtStateThree_eq_657_celsius
    (setup : HeliumPVProcessSetup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesProcessSemantics setup)
    (_data : HasScenarioAndFigureData setup) :
    temperatureInCelsius (setup.state .three).temperature = 657 := by
  have hT :
      (setup.state .two).temperature = (setup.state .three).temperature := by
    simpa only [ProcessLeg.initialState, ProcessLeg.finalState] using
      _laws.isothermalPreservesTemperature .twoToThree
        _data.secondLegIsIsothermal
  calc
    temperatureInCelsius (setup.state .three).temperature =
        temperatureInCelsius (setup.state .two).temperature :=
      congrArg temperatureInCelsius hT.symm
    _ = 657 := _data.stateTwoTemperatureIs657Celsius

end PhyXMiniProblems.ProblemPhyXMini0367
