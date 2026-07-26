import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0488

open Dimension

/-!
# Junction temperature of equal copper and aluminum rods

A copper rod and an aluminum rod of equal length and cross-sectional area are
joined end to end.  The copper outer end is held at `205 °C` by a furnace and
the aluminum outer end at `0 °C` by an ice bath.  The supplied figure places
copper on the left, aluminum on the right, and marks the junction by `T = ?`.

The physical model is ideal steady one-dimensional conduction with perfect
contacts and no lateral heat loss.  Lengths, areas, heat currents, and thermal
conductivities are unit-independent Physlib quantities.  Physlib's absolute
`Temperature` remains the temperature primitive; Celsius values are affine
instrument readouts attached to that primitive.

Assumption/target split:

* governing laws: perfect thermal contact, zero lateral loss, common steady
  axial heat current, and Fourier's law in each homogeneous rod;
* previous-part results: none;
* data and figure readouts: rod order and labels, equal lengths and areas,
  endpoint temperatures, and the fact that the junction value is unknown;
* target conclusion: the junction temperature expressed in terms of the two
  unspecified material conductivities.  The displayed choices and recorded
  answer are retained only as dataset metadata.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical length, independent of a choice of unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative heat-transfer rate, with the physical dimension of power. -/
abbrev HeatCurrentQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Thermal conductivity, whose coherent SI unit is watt per metre-kelvin. -/
abbrev ThermalConductivityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read an area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a heat current in the coherent unit determined by the base units. -/
def heatCurrentReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (heatCurrent : HeatCurrentQuantity) : ℝ :=
  ((heatCurrent {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read thermal conductivity in the coherent unit determined by the base units. -/
def thermalConductivityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (temperatureUnit : TemperatureUnit)
    (conductivity : ThermalConductivityQuantity) : ℝ :=
  ((conductivity {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit,
    temperature := temperatureUnit}).val : ℝ)

/-- Metre readout of a physical rod length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Square-metre readout of a physical cross-sectional area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Watt readout of a physical axial heat current. -/
def heatCurrentInWatts (heatCurrent : HeatCurrentQuantity) : ℝ :=
  heatCurrentReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
    heatCurrent

/-- Watt-per-metre-kelvin readout of a physical conductivity. -/
def thermalConductivityInWattsPerMeterKelvin
    (conductivity : ThermalConductivityQuantity) : ℝ :=
  thermalConductivityReadout MassUnit.kilograms LengthUnit.meters
    TimeUnit.seconds TemperatureUnit.kelvin conductivity

/-!
Physlib models absolute temperature in a zero-preserving scale, while Celsius
is affine.  This record retains the absolute physical quantity and explicitly
calibrates the scalar thermometer readout to kelvins.
-/
structure CelsiusTemperatureReading where
  absoluteTemperature : Temperature
  degreesCelsius : ℝ
  kelvinCalibration :
    absoluteTemperature.toReal = degreesCelsius + 27315 / 100

/-! ## Rods, thermal locations, and primary-image vocabulary -/

/-- The two end-to-end sections shown in the supplied image. -/
inductive RodSection where
  | copperSection
  | aluminumSection
  deriving DecidableEq, Fintype, Repr

/-- The two materials named in the problem. -/
inductive RodMaterial where
  | copper
  | aluminum
  deriving DecidableEq, Fintype, Repr

/-- Thermally distinct locations from the furnace to the ice bath. -/
inductive ThermalLocation where
  | furnaceReservoir
  | copperHotEnd
  | copperJunctionSide
  | aluminumJunctionSide
  | aluminumColdEnd
  | iceBathReservoir
  deriving DecidableEq, Fintype, Repr

/-- The three thermal interfaces along the series heat-flow path. -/
inductive ThermalContact where
  | furnaceToCopper
  | copperToAluminum
  | aluminumToIceBath
  deriving DecidableEq, Fintype, Repr

/-- Quality of a thermal interface. -/
inductive ContactQuality where
  | perfect
  | nonideal
  deriving DecidableEq, Repr

/-- Mechanical arrangement of the two rods. -/
inductive RodArrangement where
  | attachedEndToEnd
  | separated
  deriving DecidableEq, Repr

/-- Time dependence of the temperature profile. -/
inductive ThermalRegime where
  | steadyState
  | transient
  deriving DecidableEq, Repr

/-- Idealized lateral boundary condition of the rods. -/
inductive RodSideCondition where
  | noLateralHeatLoss
  | heatExchanging
  deriving DecidableEq, Repr

/-- The two constant-temperature devices named in the prose. -/
inductive ReservoirKind where
  | furnace
  | iceBath
  deriving DecidableEq, Repr

/-- The locations joined by each thermal contact. -/
def contactLocations : ThermalContact → ThermalLocation × ThermalLocation
  | .furnaceToCopper => (.furnaceReservoir, .copperHotEnd)
  | .copperToAluminum => (.copperJunctionSide, .aluminumJunctionSide)
  | .aluminumToIceBath => (.aluminumColdEnd, .iceBathReservoir)

/-- Hot-side location of each rod section. -/
def sectionHotLocation : RodSection → ThermalLocation
  | .copperSection => .copperHotEnd
  | .aluminumSection => .aluminumJunctionSide

/-- Cold-side location of each rod section. -/
def sectionColdLocation : RodSection → ThermalLocation
  | .copperSection => .copperJunctionSide
  | .aluminumSection => .aluminumColdEnd

/-- Physical objects visibly represented in the supplied raster. -/
inductive FigureObject where
  | copperRod
  | aluminumRod
  | copperAluminumJunction
  deriving DecidableEq, Fintype, Repr

/-- Literal labels and numerical marks printed in the supplied raster. -/
inductive FigureLabel where
  | copperCu
  | aluminumAl
  | hotTemperature205C
  | junctionTemperatureUnknownT
  | coldTemperature0C
  deriving DecidableEq, Fintype, Repr

/-- Qualitative and label-level evidence transcribed from the primary image. -/
structure CompositeRodFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  copperIsLeftOfAluminum : Bool
  rodsTouchAtJunction : Bool
  hotMarkIsAtCopperOuterEnd : Bool
  coldMarkIsAtAluminumOuterEnd : Bool
  junctionLabel : FigureLabel

/-! ## Independent setup and premise interfaces -/

/-!
Independent physical data for the apparatus.  In particular, neither junction
temperature is defined from `130 °C` or from any answer-choice value.
-/
structure CompositeRodSetup where
  sectionLength : RodSection → LengthQuantity
  sectionArea : RodSection → AreaQuantity
  sectionMaterial : RodSection → RodMaterial
  materialConductivity : RodMaterial → ThermalConductivityQuantity
  temperatureAt : ThermalLocation → CelsiusTemperatureReading
  sectionHeatCurrent : RodSection → HeatCurrentQuantity
  commonAxialHeatCurrent : HeatCurrentQuantity
  lateralHeatLoss : HeatCurrentQuantity
  contactQuality : ThermalContact → ContactQuality
  arrangement : RodArrangement
  regime : ThermalRegime
  sideCondition : RodSideCondition
  hotReservoir : ReservoirKind
  coldReservoir : ReservoirKind
  figure : CompositeRodFigure

/-- Categorical apparatus and idealized thermal regime used by the model. -/
structure MatchesCompositeRodScenario (setup : CompositeRodSetup) : Prop where
  copperSectionMaterial :
    setup.sectionMaterial .copperSection = .copper
  aluminumSectionMaterial :
    setup.sectionMaterial .aluminumSection = .aluminum
  rodsAttachedEndToEnd : setup.arrangement = .attachedEndToEnd
  furnaceOnCopperSide : setup.hotReservoir = .furnace
  iceBathOnAluminumSide : setup.coldReservoir = .iceBath
  steadyStateEstablished : setup.regime = .steadyState
  noLateralHeatExchange : setup.sideCondition = .noLateralHeatLoss
  everyContactPerfect :
    ∀ contact, setup.contactQuality contact = .perfect

/-!
Primary-image evidence.  The junction is recorded only as the unknown label
`T = ?`; no numerical junction temperature occurs in this interface.
-/
structure MatchesSuppliedFigure (setup : CompositeRodSetup) : Prop where
  everyNamedObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everyPrintedLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  copperShownLeftOfAluminum :
    setup.figure.copperIsLeftOfAluminum = true
  sectionsMeetAtJunction : setup.figure.rodsTouchAtJunction = true
  hotMarkAtCopperOuterEnd :
    setup.figure.hotMarkIsAtCopperOuterEnd = true
  coldMarkAtAluminumOuterEnd :
    setup.figure.coldMarkIsAtAluminumOuterEnd = true
  junctionMarkedUnknown :
    setup.figure.junctionLabel = .junctionTemperatureUnknownT

/-!
Geometry and endpoint temperature readouts stated in the problem.  The common
length and area need no numerical values because they cancel in the series
steady-state balance.
-/
structure MatchesProblemReadouts (setup : CompositeRodSetup) : Prop where
  equalRodLengths :
    setup.sectionLength .copperSection =
      setup.sectionLength .aluminumSection
  equalCrossSectionalAreas :
    setup.sectionArea .copperSection = setup.sectionArea .aluminumSection
  furnaceCelsius :
    (setup.temperatureAt .furnaceReservoir).degreesCelsius = 205
  copperOuterEndCelsius :
    (setup.temperatureAt .copperHotEnd).degreesCelsius = 205
  aluminumOuterEndCelsius :
    (setup.temperatureAt .aluminumColdEnd).degreesCelsius = 0
  iceBathCelsius :
    (setup.temperatureAt .iceBathReservoir).degreesCelsius = 0

/-- Positivity and hot-to-cold ordering required by the conduction model. -/
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
  absoluteTemperaturesPositive :
    ∀ location,
      0 < (setup.temperatureAt location).absoluteTemperature.toReal
  hotBoundaryAboveColdBoundary :
    (setup.temperatureAt .copperHotEnd).degreesCelsius >
      (setup.temperatureAt .aluminumColdEnd).degreesCelsius

/-!
A perfect contact equates the physical temperature readings on its two sides.
This general interface contains no numerical junction-temperature value.
-/
structure SatisfiesPerfectThermalContactLaw
    (setup : CompositeRodSetup) : Prop where
  temperaturesAgree :
    ∀ contact,
      setup.contactQuality contact = .perfect →
        setup.temperatureAt (contactLocations contact).1 =
          setup.temperatureAt (contactLocations contact).2

/-!
Steady one-dimensional Fourier conduction in each homogeneous rod section:

`heat current = conductivity * area * temperature drop / length`.

The same independent axial current passes through both series sections, and
the ideal side condition makes lateral loss zero.  These are governing laws,
not a restatement of the requested junction temperature.
-/
structure SatisfiesSteadySeriesFourierConduction
    (setup : CompositeRodSetup) : Prop where
  noLateralHeatLoss : heatCurrentInWatts setup.lateralHeatLoss = 0
  commonCurrentThroughBothSections :
    ∀ rodSection,
      setup.sectionHeatCurrent rodSection = setup.commonAxialHeatCurrent
  fourierLawForEachSection :
    ∀ rodSection,
      heatCurrentInWatts (setup.sectionHeatCurrent rodSection) =
        thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity (setup.sectionMaterial rodSection)) *
          areaInSquareMeters (setup.sectionArea rodSection) *
          ((setup.temperatureAt (sectionHotLocation rodSection)).degreesCelsius -
            (setup.temperatureAt
              (sectionColdLocation rodSection)).degreesCelsius) /
          lengthInMeters (setup.sectionLength rodSection)

/-! ## Derived temperature and answer-choice metadata -/

/-- Celsius readout on the copper side of the perfect Cu--Al junction. -/
def junctionTemperatureInDegreesCelsius (setup : CompositeRodSetup) : ℝ :=
  (setup.temperatureAt .copperJunctionSide).degreesCelsius

/-!
The source itself identifies the two materials but does not print a numerical
conductivity table.  Before adding any textbook calibration, steady series
conduction therefore determines the junction temperature symbolically as

`T = 205 * k_Cu / (k_Cu + k_Al)`.

This is the strongest numerical-readout conclusion supported by the stated
apparatus, endpoint temperatures, and governing laws alone.  In particular,
neither a conductivity value nor an answer-choice value is a premise here.
-/
theorem junction_temperature_from_conductivities
    (setup : CompositeRodSetup)
    (hScenario : MatchesCompositeRodScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalCompositeRodParameters setup)
    (hContact : SatisfiesPerfectThermalContactLaw setup)
    (hFourier : SatisfiesSteadySeriesFourierConduction setup) :
    junctionTemperatureInDegreesCelsius setup =
      205 * thermalConductivityInWattsPerMeterKelvin
          (setup.materialConductivity .copper) /
        (thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity .copper) +
          thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity .aluminum)) := by
  sorry

/-- Labels of the four answer choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Celsius value printed beside each supplied answer label. -/
def displayedJunctionTemperatureCelsius : AnswerChoice → ℝ
  | .A => 100
  | .B => 110
  | .C => 120
  | .D => 130

/-- Dataset metadata recording the supplied answer label.  It is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The source and primary image provide no numerical thermal conductivities.
Equality of the two Fourier heat currents, together with equal rod lengths and
areas, therefore determines the junction temperature only in terms of the
independent copper and aluminum conductivity readouts:

`T = 205 * k_Cu / (k_Cu + k_Al)`.

This declaration formalizes `thm:physics:phyx_mini_0488:target` at the strongest
level supported by the supplied evidence.  It neither assumes nor concludes a
particular answer choice.  The recorded choice `D` remains metadata above.
-/
theorem problem_phyx_mini_0488
    (setup : CompositeRodSetup)
    (hScenario : MatchesCompositeRodScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalCompositeRodParameters setup)
    (hContact : SatisfiesPerfectThermalContactLaw setup)
    (hFourier : SatisfiesSteadySeriesFourierConduction setup) :
    junctionTemperatureInDegreesCelsius setup =
      205 * thermalConductivityInWattsPerMeterKelvin
          (setup.materialConductivity .copper) /
        (thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity .copper) +
          thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity .aluminum)) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0488
