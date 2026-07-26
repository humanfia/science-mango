import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0331

open Dimension

/-!
# Steel length in an insulated copper--steel composite rod

A copper section and a steel section are joined in series between boiling
water and an ice--water mixture.  In steady state, insulation prevents lateral
heat loss and the same axial heat current passes through both sections.  The
question asks for the steel length from the measured junction temperature.

The supplied source and figure do not give numerical thermal
conductivities.  Consequently the source-supported conclusion below is the
exact steel-length relation in terms of the two material conductivities; the
recorded numerical answer is retained only as dataset metadata.

Lengths, areas, heat currents, and thermal conductivities below are
unit-independent Physlib quantities.  Physlib's absolute `Temperature` is
retained as the physical primitive; Celsius numbers are explicitly instrument
readouts.  The requested steel length is an independent setup field related to
the other quantities only by the governing contact and Fourier-law interfaces.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- A nonnegative physical length, independent of the selected unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative cross-sectional area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative heat-transfer rate (power), with dimension
`mass * length^2 / time^3`. -/
abbrev HeatCurrentQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Thermal conductivity, with SI unit watt per meter-kelvin and dimension
`mass * length / (time^3 * temperature)`. -/
abbrev ThermalConductivityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Square-meter readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Square-centimeter readout of a physical area. -/
def areaInSquareCentimeters (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- SI watt readout of a heat current. -/
def heatCurrentInWatts (heatCurrent : HeatCurrentQuantity) : ℝ :=
  ((heatCurrent UnitChoices.SI).val : ℝ)

/-- SI watt-per-meter-kelvin readout of thermal conductivity. -/
def thermalConductivityInWattsPerMeterKelvin
    (conductivity : ThermalConductivityQuantity) : ℝ :=
  ((conductivity UnitChoices.SI).val : ℝ)

/-!
Physlib stores an absolute, nonnegative physical temperature.  Celsius has an
affine offset and Physlib currently supplies no offset-Celsius measurement
API, so the figure's Celsius value is retained as a named scalar instrument
readout rather than replacing the physical temperature by `ℝ`.
-/
structure MeasuredTemperature where
  absoluteTemperature : Temperature
  celsiusReadout : ℝ

/-! ## Rod, reservoir, contact, and figure vocabulary -/

/-- The two material kinds named in the rod. -/
inductive RodMaterial where
  | copper
  | steel
  deriving DecidableEq, Repr

/-- The two end-to-end sections of the composite rod. -/
inductive RodSection where
  | copperSection
  | steelSection
  deriving DecidableEq, Repr

/-- Thermally distinguished locations in the apparatus. -/
inductive ThermalLocation where
  | boilingWater
  | copperHotEnd
  | copperJunctionSide
  | steelJunctionSide
  | steelColdEnd
  | iceWaterMixture
  deriving DecidableEq, Repr

/-- The three interfaces described as being in perfect thermal contact. -/
inductive ThermalContact where
  | boilingWaterToCopper
  | copperToSteel
  | steelToIceWater
  deriving DecidableEq, Repr

/-- Physical quality of a thermal interface. -/
inductive ContactQuality where
  | perfect
  | nonideal
  deriving DecidableEq, Repr

/-- Water-pressure regime at the boiling reservoir. -/
inductive WaterPressureRegime where
  | atmospheric
  | other
  deriving DecidableEq, Repr

/-- Time dependence of the temperature profile. -/
inductive ThermalRegime where
  | steadyState
  | transient
  deriving DecidableEq, Repr

/-- Lateral boundary condition of the rod. -/
inductive RodSideCondition where
  | insulated
  | heatExchanging
  deriving DecidableEq, Repr

/-- The two physical locations joined by each contact. -/
def contactLocations : ThermalContact → ThermalLocation × ThermalLocation
  | .boilingWaterToCopper => (.boilingWater, .copperHotEnd)
  | .copperToSteel => (.copperJunctionSide, .steelJunctionSide)
  | .steelToIceWater => (.steelColdEnd, .iceWaterMixture)

/-- Hot-side location of each rod section. -/
def sectionHotLocation : RodSection → ThermalLocation
  | .copperSection => .copperHotEnd
  | .steelSection => .steelJunctionSide

/-- Cold-side location of each rod section. -/
def sectionColdLocation : RodSection → ThermalLocation
  | .copperSection => .copperJunctionSide
  | .steelSection => .steelColdEnd

/-- Physical objects visibly depicted in the supplied raster. -/
inductive FigureObject where
  | boilingWaterBath
  | copperRodSection
  | steelRodSection
  | lateralInsulation
  | iceWaterBath
  deriving DecidableEq, Repr

/-- Text or numerical labels printed in the supplied raster. -/
inductive FigureLabel where
  | boilingWater
  | insulation
  | copper
  | junction65C
  | steel
  | iceAndWater
  | copperLengthOneMeter
  | steelLengthL2
  deriving DecidableEq, Repr

/-!
Qualitative information from the primary image.  The image labels the copper
length and the unknown steel length, locates `65.0 °C` at the junction, and
shows insulation around the rod sides.  It does not print the common area or
either material's conductivity.
-/
structure CompositeRodFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  copperTouchesBoilingWater : Bool
  copperJoinedEndToEndWithSteel : Bool
  steelTouchesIceWater : Bool
  insulationCoversCopperSides : Bool
  insulationCoversSteelSides : Bool
  junctionTemperatureLabel : FigureLabel
  copperLengthArrowLabel : FigureLabel
  steelLengthArrowLabel : FigureLabel
  containsCrossSectionAreaReadout : Bool
  containsConductivityReadout : Bool

/-! ## Independent setup and assumption interfaces -/

/-!
Independent quantities and categorical data for the apparatus.  In
particular, `sectionLength .steelSection` is not defined from the displayed
answer or from a conductivity formula.
-/
structure CompositeRodSetup where
  sectionLength : RodSection → LengthQuantity
  sectionArea : RodSection → AreaQuantity
  sectionMaterial : RodSection → RodMaterial
  materialConductivity : RodMaterial → ThermalConductivityQuantity
  temperatureAt : ThermalLocation → MeasuredTemperature
  axialHeatCurrent : HeatCurrentQuantity
  lateralHeatLoss : HeatCurrentQuantity
  contactQuality : ThermalContact → ContactQuality
  boilingWaterPressure : WaterPressureRegime
  regime : ThermalRegime
  sideCondition : RodSideCondition
  figure : CompositeRodFigure

/-- Categorical scenario stated in the prose. -/
structure MatchesCompositeRodScenario (setup : CompositeRodSetup) : Prop where
  copperSectionMaterial :
    setup.sectionMaterial .copperSection = .copper
  steelSectionMaterial :
    setup.sectionMaterial .steelSection = .steel
  boilingAtAtmosphericPressure :
    setup.boilingWaterPressure = .atmospheric
  steadyStateEstablished : setup.regime = .steadyState
  sidesInsulated : setup.sideCondition = .insulated
  everyContactPerfect :
    ∀ contact, setup.contactQuality contact = .perfect

/-- Detailed evidence transcribed from the primary raster. -/
structure MatchesSuppliedFigure (setup : CompositeRodSetup) : Prop where
  everyNamedObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everyPrintedLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  copperTouchesBoilingWater :
    setup.figure.copperTouchesBoilingWater = true
  sectionsJoinedEndToEnd :
    setup.figure.copperJoinedEndToEndWithSteel = true
  steelTouchesIceWater : setup.figure.steelTouchesIceWater = true
  copperSidesShownInsulated :
    setup.figure.insulationCoversCopperSides = true
  steelSidesShownInsulated :
    setup.figure.insulationCoversSteelSides = true
  temperatureLabelAtJunction :
    setup.figure.junctionTemperatureLabel = .junction65C
  oneMeterLabelSpansCopper :
    setup.figure.copperLengthArrowLabel = .copperLengthOneMeter
  L2LabelSpansSteel :
    setup.figure.steelLengthArrowLabel = .steelLengthL2
  noAreaPrinted : setup.figure.containsCrossSectionAreaReadout = false
  noConductivityPrinted :
    setup.figure.containsConductivityReadout = false

/-!
Numerical geometry and thermometer readouts explicitly given by the problem.
The steel length is deliberately absent.
-/
structure MatchesProblemReadouts (setup : CompositeRodSetup) : Prop where
  copperLengthMeters :
    lengthInMeters (setup.sectionLength .copperSection) = 1
  copperAreaSquareCentimeters :
    areaInSquareCentimeters (setup.sectionArea .copperSection) = 4
  steelAreaSquareCentimeters :
    areaInSquareCentimeters (setup.sectionArea .steelSection) = 4
  copperSideJunctionCelsius :
    (setup.temperatureAt .copperJunctionSide).celsiusReadout = 65

/-!
At atmospheric pressure, boiling water supplies the `100 °C` fixed point and
an equilibrated ice--water mixture supplies the `0 °C` fixed point.  These are
boundary-temperature calibrations, not assumptions about the steel length.
-/
structure UsesAtmosphericWaterFixedPoints
    (setup : CompositeRodSetup) : Prop where
  boilingWaterCelsius :
    (setup.temperatureAt .boilingWater).celsiusReadout = 100
  iceWaterMixtureCelsius :
    (setup.temperatureAt .iceWaterMixture).celsiusReadout = 0

/-!
Physlib's `Temperature.toReal` reads the nonnegative absolute-temperature
coordinate without an affine Celsius offset.  This calibration states that,
for this setup, that coordinate is being read in kelvins and relates it to the
separately reported Celsius instrument value.  It is a general measurement
law and contains no information about the steel length.
-/
structure SatisfiesKelvinCelsiusCalibration
    (setup : CompositeRodSetup) : Prop where
  kelvinEqualsCelsiusPlusOffset :
    ∀ location,
      Temperature.toReal
          (setup.temperatureAt location).absoluteTemperature =
        (setup.temperatureAt location).celsiusReadout + 27315 / 100

/-- Strict positivity and the hot-to-cold ordering needed by the conduction
model.  None of these conditions fixes the unknown steel length. -/
structure HasPhysicalCompositeRodParameters
    (setup : CompositeRodSetup) : Prop where
  sectionLengthsPositive :
    ∀ rodSection, 0 < lengthInMeters (setup.sectionLength rodSection)
  sectionAreasPositive :
    ∀ rodSection, 0 < areaInSquareMeters (setup.sectionArea rodSection)
  conductivitiesPositive :
    ∀ material,
      0 < thermalConductivityInWattsPerMeterKelvin
        (setup.materialConductivity material)
  axialHeatCurrentPositive : 0 < heatCurrentInWatts setup.axialHeatCurrent
  absoluteTemperaturesPositive :
    ∀ location,
      0 < Temperature.toReal
        (setup.temperatureAt location).absoluteTemperature
  hotReservoirAboveJunction :
    (setup.temperatureAt .boilingWater).celsiusReadout >
      (setup.temperatureAt .copperJunctionSide).celsiusReadout
  junctionAboveColdReservoir :
    (setup.temperatureAt .steelJunctionSide).celsiusReadout >
      (setup.temperatureAt .iceWaterMixture).celsiusReadout

/-!
A perfect contact makes the two physical temperature measurements on its
sides agree.  This is a general interface law over all three contacts and
contains no length formula.
-/
structure SatisfiesPerfectThermalContactLaw
    (setup : CompositeRodSetup) : Prop where
  temperaturesAgree :
    ∀ contact,
      setup.contactQuality contact = .perfect →
        setup.temperatureAt (contactLocations contact).1 =
          setup.temperatureAt (contactLocations contact).2

/-!
Steady one-dimensional Fourier conduction in each homogeneous section:

`heat current = conductivity * area * temperature drop / length`.

The same independent `axialHeatCurrent` occurs for both sections, expressing
continuity of heat flow in the steady series arrangement.  The lateral loss
readout is zero because of insulation.  The law contains neither `0.242 m`
nor any answer-choice relation.
-/
structure SatisfiesInsulatedSteadyFourierConduction
    (setup : CompositeRodSetup) : Prop where
  noLateralHeatLoss : heatCurrentInWatts setup.lateralHeatLoss = 0
  fourierLawForEachSection :
    ∀ rodSection,
      heatCurrentInWatts setup.axialHeatCurrent =
        thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity (setup.sectionMaterial rodSection)) *
          areaInSquareMeters (setup.sectionArea rodSection) *
          ((setup.temperatureAt (sectionHotLocation rodSection)).celsiusReadout -
            (setup.temperatureAt
              (sectionColdLocation rodSection)).celsiusReadout) /
          lengthInMeters (setup.sectionLength rodSection)

/-! ## Derived length and recorded multiple-choice metadata -/

/-- The exact source-supported steel-length expression.  The material
conductivities remain symbolic because neither the problem text nor the
figure supplies their numerical values. -/
theorem steelLength_exact_from_steady_conduction
    (setup : CompositeRodSetup)
    (hScenario : MatchesCompositeRodScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hWater : UsesAtmosphericWaterFixedPoints setup)
    (hTemperatureCalibration : SatisfiesKelvinCelsiusCalibration setup)
    (hPhysical : HasPhysicalCompositeRodParameters setup)
    (hContact : SatisfiesPerfectThermalContactLaw setup)
    (hFourier : SatisfiesInsulatedSteadyFourierConduction setup) :
    lengthInMeters (setup.sectionLength .steelSection) =
      (thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity .steel) *
          (65 - 0) * 1) /
        (thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity .copper) *
          (100 - 65)) := by
  sorry

/-- Labels of the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Meter value printed beside each answer choice. -/
def displayedLengthInMeters : AnswerChoice → ℝ
  | .A => 121 / 500
  | .B => 111 / 500
  | .C => 71 / 500
  | .D => 131 / 500

/-- Dataset metadata recording that the supplied answer label is `A`. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- Agreement with a three-decimal-place meter display: the actual length is
within half a millimeter of the displayed value. -/
def RoundsToDisplayedMillimeter
    (length : LengthQuantity) (displayedMeters : ℝ) : Prop :=
  |lengthInMeters length - displayedMeters| < (1 / 2000 : ℝ)

/-- The steel length rounds to the number printed for an answer choice. -/
def MatchesAnswerChoice
    (setup : CompositeRodSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedMillimeter (setup.sectionLength .steelSection)
    (displayedLengthInMeters choice)

/-!
The source-supported conclusion determines the steel length symbolically from
the conductivity ratio.  Selecting a numerical answer choice would require a
conductivity table not present in the supplied text or raster.  The target
therefore does not assert that the recorded answer follows from the stated
data.

This is the redrafted formal target corresponding to
`thm:physics:phyx_mini_0331:target`.
-/
theorem problem_phyx_mini_0331
    (setup : CompositeRodSetup)
    (hScenario : MatchesCompositeRodScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hWater : UsesAtmosphericWaterFixedPoints setup)
    (hTemperatureCalibration : SatisfiesKelvinCelsiusCalibration setup)
    (hPhysical : HasPhysicalCompositeRodParameters setup)
    (hContact : SatisfiesPerfectThermalContactLaw setup)
    (hFourier : SatisfiesInsulatedSteadyFourierConduction setup) :
    lengthInMeters (setup.sectionLength .steelSection) =
      (thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity .steel) *
          (65 - 0) * 1) /
        (thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity .copper) *
          (100 - 65)) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0331
