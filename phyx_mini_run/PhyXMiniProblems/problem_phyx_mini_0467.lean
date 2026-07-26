import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0467

open Dimension

/-!
# Heat flow through welded steel and copper bars

A steel bar and a copper bar are welded end to end between steam and ice.
Their sides are insulated, so the steady heat flow is one-dimensional and the
same heat current passes through both sections.  The figure places the steel
on the left, the copper on the right, and labels the unknown junction
temperature by `T`.

The supplied source does not give numerical thermal conductivities for either
material.  Consequently the physical conclusion below is the exact heat-rate
relation as a function of those two material properties; the recorded answer
choice is retained only as dataset metadata.

Physical lengths, areas, heat currents, and conductivities below carry their
dimensions independently of a choice of units.  Physlib's absolute
`Temperature` remains the physical temperature primitive.  Celsius numbers
are named instrument readouts because Celsius is an affine temperature scale.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical length, independent of the selected unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical cross-sectional area, using Physlib's area type. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative rate of heat transfer, dimensionally a power. -/
abbrev HeatFlowRateQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Thermal conductivity, with SI unit watt per meter-kelvin. -/
abbrev ThermalConductivityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a heat-flow rate in the coherent power unit selected by the three
base-unit arguments. -/
def heatFlowRateReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (rate : HeatFlowRateQuantity) : ℝ :=
  ((rate {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a conductivity in the coherent unit selected by the four base-unit
arguments. -/
def thermalConductivityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (temperatureUnit : TemperatureUnit)
    (conductivity : ThermalConductivityQuantity) : ℝ :=
  ((conductivity {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit,
    temperature := temperatureUnit}).val : ℝ)

/-- Centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Square-centimeter readout of a physical area. -/
def areaInSquareCentimeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.centimeters area

/-- Square-meter readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Watt readout of a physical heat-flow rate. -/
def heatFlowRateInWatts (rate : HeatFlowRateQuantity) : ℝ :=
  heatFlowRateReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds rate

/-- Watt-per-meter-kelvin readout of a physical thermal conductivity. -/
def thermalConductivityInWattsPerMeterKelvin
    (conductivity : ThermalConductivityQuantity) : ℝ :=
  thermalConductivityReadout MassUnit.kilograms LengthUnit.meters
    TimeUnit.seconds TemperatureUnit.kelvin conductivity

/-- A physical absolute temperature paired with the Celsius number displayed
by a thermometer or printed in the figure.  The final field records the
affine Kelvin--Celsius calibration, which is not represented by Physlib's
zero-preserving `TemperatureUnit` scaling. -/
structure MeasuredTemperature where
  absoluteTemperature : Temperature
  celsiusReadout : ℝ
  kelvinCelsiusCalibration :
    Temperature.toReal absoluteTemperature = celsiusReadout + 27315 / 100

/-! ## Apparatus, material, and figure vocabulary -/

/-- The two materials named in the problem. -/
inductive BarMaterial where
  | steel
  | copper
  deriving DecidableEq, Repr

/-- The two end-to-end sections of the composite bar. -/
inductive BarSection where
  | steelSection
  | copperSection
  deriving DecidableEq, Repr

/-- Thermally distinguished locations in the apparatus. -/
inductive ThermalLocation where
  | steamReservoir
  | steelHotEnd
  | steelJunctionSide
  | copperJunctionSide
  | copperColdEnd
  | iceReservoir
  deriving DecidableEq, Repr

/-- The three thermal contacts along the heat-flow path. -/
inductive ThermalContact where
  | steamToSteel
  | steelCopperWeld
  | copperToIce
  deriving DecidableEq, Repr

/-- Quality of a thermal interface. -/
inductive ContactQuality where
  | perfect
  | nonideal
  deriving DecidableEq, Repr

/-- Mechanical relation between the two bar sections. -/
inductive SectionConnection where
  | weldedEndToEnd
  | separated
  deriving DecidableEq, Repr

/-- Time dependence of the temperature profile. -/
inductive ThermalRegime where
  | steadyState
  | transient
  deriving DecidableEq, Repr

/-- Lateral boundary condition on the bars. -/
inductive BarSideCondition where
  | perfectlyInsulated
  | heatExchanging
  deriving DecidableEq, Repr

/-- Thermal reservoirs named in the prose. -/
inductive ReservoirKind where
  | steam
  | ice
  deriving DecidableEq, Repr

/-- The two locations joined by each thermal contact. -/
def contactLocations : ThermalContact → ThermalLocation × ThermalLocation
  | .steamToSteel => (.steamReservoir, .steelHotEnd)
  | .steelCopperWeld => (.steelJunctionSide, .copperJunctionSide)
  | .copperToIce => (.copperColdEnd, .iceReservoir)

/-- The hot-side location of each material section. -/
def sectionHotLocation : BarSection → ThermalLocation
  | .steelSection => .steelHotEnd
  | .copperSection => .copperJunctionSide

/-- The cold-side location of each material section. -/
def sectionColdLocation : BarSection → ThermalLocation
  | .steelSection => .steelJunctionSide
  | .copperSection => .copperColdEnd

/-- Physical objects visibly represented in the supplied figure. -/
inductive FigureObject where
  | steelBar
  | copperBar
  | steelCopperSeparator
  | hotBoundaryWall
  | coldBoundaryWall
  deriving DecidableEq, Repr

/-- Text and numerical labels printed in the supplied figure. -/
inductive FigureLabel where
  | steel
  | copper
  | hotTemperature100C
  | junctionTemperatureT
  | coldTemperature0C
  | steelLength10cm
  | copperLength20cm
  | commonHeight2cm
  deriving DecidableEq, Repr

/-- Qualitative and label-level data transcribed from the supplied raster. -/
structure CompositeBarFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  steelIsLeftOfCopper : Bool
  sectionsTouchAtSeparator : Bool
  hotBoundaryTouchesSteel : Bool
  coldBoundaryTouchesCopper : Bool
  junctionLabel : FigureLabel
  verticalSizeLabel : FigureLabel
  steelLengthArrowLabel : FigureLabel
  copperLengthArrowLabel : FigureLabel

/-! ## Independent setup and assumption interfaces -/

/-- Independent physical data for the apparatus.  In particular, the total
heat-flow rate is not defined from any answer-choice value. -/
structure CompositeBarSetup where
  sectionLength : BarSection → LengthQuantity
  crossSectionSide : LengthQuantity
  sectionArea : BarSection → AreaQuantity
  sectionMaterial : BarSection → BarMaterial
  materialConductivity : BarMaterial → ThermalConductivityQuantity
  temperatureAt : ThermalLocation → MeasuredTemperature
  sectionHeatFlowRate : BarSection → HeatFlowRateQuantity
  totalHeatFlowRate : HeatFlowRateQuantity
  lateralHeatLossRate : HeatFlowRateQuantity
  contactQuality : ThermalContact → ContactQuality
  connection : SectionConnection
  regime : ThermalRegime
  sideCondition : BarSideCondition
  hotReservoir : ReservoirKind
  coldReservoir : ReservoirKind
  figure : CompositeBarFigure

/-- The categorical apparatus described in the problem statement. -/
structure MatchesCompositeBarScenario (setup : CompositeBarSetup) : Prop where
  steelSectionMaterial : setup.sectionMaterial .steelSection = .steel
  copperSectionMaterial : setup.sectionMaterial .copperSection = .copper
  barsWeldedEndToEnd : setup.connection = .weldedEndToEnd
  steadyState : setup.regime = .steadyState
  sidesPerfectlyInsulated : setup.sideCondition = .perfectlyInsulated
  hotBathIsSteam : setup.hotReservoir = .steam
  coldBathIsIce : setup.coldReservoir = .ice
  everyContactPerfect :
    ∀ contact, setup.contactQuality contact = .perfect

/-- Evidence transcribed from the primary figure, including the unknown
junction label `T` but no numerical junction-temperature assumption. -/
structure MatchesSuppliedFigure (setup : CompositeBarSetup) : Prop where
  everyNamedObjectShown : ∀ object, setup.figure.showsObject object = true
  everyPrintedLabelShown : ∀ label, setup.figure.showsLabel label = true
  steelShownLeftOfCopper : setup.figure.steelIsLeftOfCopper = true
  sectionsMeetAtSeparator : setup.figure.sectionsTouchAtSeparator = true
  hotBoundaryAtSteel : setup.figure.hotBoundaryTouchesSteel = true
  coldBoundaryAtCopper : setup.figure.coldBoundaryTouchesCopper = true
  separatorMarkedT : setup.figure.junctionLabel = .junctionTemperatureT
  heightMarkedTwoCentimeters :
    setup.figure.verticalSizeLabel = .commonHeight2cm
  steelLengthMarkedTenCentimeters :
    setup.figure.steelLengthArrowLabel = .steelLength10cm
  copperLengthMarkedTwentyCentimeters :
    setup.figure.copperLengthArrowLabel = .copperLength20cm

/-- Geometry and boundary-temperature readouts stated in the prose and
printed in the figure.  The area equation records the stated square section. -/
structure MatchesProblemReadouts (setup : CompositeBarSetup) : Prop where
  steelLengthCentimeters :
    lengthInCentimeters (setup.sectionLength .steelSection) = 10
  copperLengthCentimeters :
    lengthInCentimeters (setup.sectionLength .copperSection) = 20
  squareSideCentimeters :
    lengthInCentimeters setup.crossSectionSide = 2
  squareAreaFromSide :
    ∀ barSection,
      areaInSquareCentimeters (setup.sectionArea barSection) =
        (lengthInCentimeters setup.crossSectionSide) ^ 2
  commonCrossSection :
    setup.sectionArea .steelSection = setup.sectionArea .copperSection
  hotBoundaryCelsius :
    (setup.temperatureAt .steelHotEnd).celsiusReadout = 100
  coldBoundaryCelsius :
    (setup.temperatureAt .copperColdEnd).celsiusReadout = 0

/-- Steam and ice provide the corresponding reservoir fixed points. -/
structure UsesSteamAndIceFixedPoints (setup : CompositeBarSetup) : Prop where
  steamCelsius :
    (setup.temperatureAt .steamReservoir).celsiusReadout = 100
  iceCelsius :
    (setup.temperatureAt .iceReservoir).celsiusReadout = 0

/-- Positivity and temperature ordering required by the conduction model. -/
structure HasPhysicalCompositeBarParameters
    (setup : CompositeBarSetup) : Prop where
  sectionLengthsPositive :
    ∀ barSection, 0 < lengthInMeters (setup.sectionLength barSection)
  sectionAreasPositive :
    ∀ barSection, 0 < areaInSquareMeters (setup.sectionArea barSection)
  conductivitiesPositive :
    ∀ material,
      0 < thermalConductivityInWattsPerMeterKelvin
        (setup.materialConductivity material)
  absoluteTemperaturesPositive :
    ∀ location,
      0 < Temperature.toReal
        (setup.temperatureAt location).absoluteTemperature
  hotBoundaryAboveColdBoundary :
    (setup.temperatureAt .steelHotEnd).celsiusReadout >
      (setup.temperatureAt .copperColdEnd).celsiusReadout

/-- A perfect thermal contact makes the temperatures on its two sides agree.
This is a general contact law and fixes no heat-flow rate. -/
structure SatisfiesPerfectThermalContactLaw
    (setup : CompositeBarSetup) : Prop where
  temperaturesAgree :
    ∀ contact,
      setup.contactQuality contact = .perfect →
        setup.temperatureAt (contactLocations contact).1 =
          setup.temperatureAt (contactLocations contact).2

/-!
Steady one-dimensional Fourier conduction in each homogeneous bar section:

`heat-flow rate = conductivity * area * temperature drop / length`.

The continuity field equates each section rate with the independent total
rate.  Perfect lateral insulation gives zero lateral heat loss.  Neither law
contains the requested `15.9 W` answer.
-/
structure SatisfiesInsulatedSteadyFourierConduction
    (setup : CompositeBarSetup) : Prop where
  noLateralHeatLoss :
    heatFlowRateInWatts setup.lateralHeatLossRate = 0
  steadyRateContinuity :
    ∀ barSection,
      setup.sectionHeatFlowRate barSection = setup.totalHeatFlowRate
  fourierLawForEachSection :
    ∀ barSection,
      heatFlowRateInWatts (setup.sectionHeatFlowRate barSection) =
        thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity (setup.sectionMaterial barSection)) *
          areaInSquareMeters (setup.sectionArea barSection) *
          ((setup.temperatureAt (sectionHotLocation barSection)).celsiusReadout -
            (setup.temperatureAt
              (sectionColdLocation barSection)).celsiusReadout) /
          lengthInMeters (setup.sectionLength barSection)

/-! ## Derived heat rate and source-supported conclusion -/

/-- Exact heat-flow rate left symbolic in the two conductivities omitted by
the source.  The supplied geometry gives section thermal resistances
`250 / k_steel` and `500 / k_copper` K/W, respectively. -/
theorem totalHeatFlowRate_exact
    (setup : CompositeBarSetup)
    (hScenario : MatchesCompositeBarScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFixedPoints : UsesSteamAndIceFixedPoints setup)
    (hPhysical : HasPhysicalCompositeBarParameters setup)
    (hContact : SatisfiesPerfectThermalContactLaw setup)
    (hFourier : SatisfiesInsulatedSteadyFourierConduction setup) :
    heatFlowRateInWatts setup.totalHeatFlowRate =
      100 /
        (250 /
            thermalConductivityInWattsPerMeterKelvin
              (setup.materialConductivity .steel) +
          500 /
            thermalConductivityInWattsPerMeterKelvin
              (setup.materialConductivity .copper)) := by
  sorry

/-- Labels of the four supplied answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Watt value printed for each answer choice. -/
def displayedHeatFlowRateInWatts : AnswerChoice → ℝ
  | .A => 128 / 10
  | .B => 159 / 10
  | .C => 175 / 10
  | .D => 195 / 10

/-- Dataset metadata recording the supplied answer label.  This definition is
not used as a premise of either physical theorem. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement with a rate displayed to the nearest tenth of a watt. -/
def RoundsToDisplayedTenthWatt
    (rate : HeatFlowRateQuantity) (displayedWatts : ℝ) : Prop :=
  |heatFlowRateInWatts rate - displayedWatts| < (1 / 20 : ℝ)

/-- The physical total heat rate rounds to the number beside an answer choice. -/
def MatchesAnswerChoice
    (setup : CompositeBarSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedTenthWatt setup.totalHeatFlowRate
    (displayedHeatFlowRateInWatts choice)

/-!
The conductivities are not included in the source, so the strongest grounded
answer is the exact series-resistance formula below.  No numerical answer
choice is asserted.  This is the formal target corresponding to
`thm:physics:phyx_mini_0467:target`.
-/
theorem problem_phyx_mini_0467
    (setup : CompositeBarSetup)
    (hScenario : MatchesCompositeBarScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFixedPoints : UsesSteamAndIceFixedPoints setup)
    (hPhysical : HasPhysicalCompositeBarParameters setup)
    (hContact : SatisfiesPerfectThermalContactLaw setup)
    (hFourier : SatisfiesInsulatedSteadyFourierConduction setup) :
    heatFlowRateInWatts setup.totalHeatFlowRate =
      100 /
        (250 /
            thermalConductivityInWattsPerMeterKelvin
              (setup.materialConductivity .steel) +
          500 /
            thermalConductivityInWattsPerMeterKelvin
              (setup.materialConductivity .copper)) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0467
