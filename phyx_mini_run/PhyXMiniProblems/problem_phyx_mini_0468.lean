import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0468

open Dimension

/-!
# Total heat current through separated copper and steel bars

The supplied image shows a copper bar and a steel bar as two spatially
separated thermal paths.  Each path connects its own `100 °C` hot end to a
`0 °C` cold end.  Thus the current requested by the problem is the sum of the
two independent steady Fourier-conduction currents, not the current through
the originally described welded series arrangement.

Lengths, cross-sectional areas, heat currents, and thermal conductivities are
represented by unit-independent Physlib quantities.  Physlib's absolute
`Temperature` is retained as the temperature primitive; real numbers occur
only in explicitly named unit readouts, temperature differences, and answer
displays.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical length, independent of the selected unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical area, carrying dimension `length²`. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative heat-transfer rate, whose coherent SI unit is the watt. -/
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

/-- Read a physical area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a heat current in the coherent power unit induced by the selected
mass, length, and time units. -/
def heatCurrentReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (heatCurrent : HeatCurrentQuantity) : ℝ :=
  ((heatCurrent {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read thermal conductivity in the coherent unit induced by the selected
base units. -/
def thermalConductivityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (temperatureUnit : TemperatureUnit)
    (conductivity : ThermalConductivityQuantity) : ℝ :=
  ((conductivity {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit,
    temperature := temperatureUnit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Square-centimetre readout of a physical area. -/
def areaInSquareCentimeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.centimeters area

/-- SI watt readout of a heat current. -/
def heatCurrentInWatts (heatCurrent : HeatCurrentQuantity) : ℝ :=
  heatCurrentReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
    heatCurrent

/-- SI watt-per-metre-kelvin readout of a thermal conductivity. -/
def thermalConductivityInWattsPerMeterKelvin
    (conductivity : ThermalConductivityQuantity) : ℝ :=
  thermalConductivityReadout MassUnit.kilograms LengthUnit.meters
    TimeUnit.seconds TemperatureUnit.kelvin conductivity

/-!
Celsius is an affine scale, whereas Physlib's `Temperature` is an absolute,
zero-preserving quantity.  This record keeps both roles and explicitly states
their kelvin calibration.
-/
structure CelsiusTemperatureReading where
  absoluteTemperature : Temperature
  degreesCelsius : ℝ
  kelvinCalibration :
    absoluteTemperature.toReal = degreesCelsius + 27315 / 100

/-! ## Bars, endpoints, and primary-figure vocabulary -/

/-- The two physical bars shown in the image. -/
inductive Bar where
  | copperBar
  | steelBar
  deriving DecidableEq, Fintype, Repr

/-- The two materials named by the problem. -/
inductive BarMaterial where
  | copper
  | steel
  deriving DecidableEq, Fintype, Repr

/-- Thermally distinguished ends of either separated bar. -/
inductive BarEnd where
  | hot
  | cold
  deriving DecidableEq, Fintype, Repr

/-- Shape of a bar's transverse cross section. -/
inductive CrossSectionShape where
  | square
  | other
  deriving DecidableEq, Repr

/-- Relative thermal arrangement of the two bars. -/
inductive BarArrangement where
  | separatedParallelPaths
  | weldedEndToEnd
  deriving DecidableEq, Repr

/-- Time dependence of the temperature profile. -/
inductive ThermalRegime where
  | steadyState
  | transient
  deriving DecidableEq, Repr

/-- Physical objects visibly present in the supplied raster. -/
inductive FigureObject where
  | copperBar
  | steelBar
  | leftHotBoundary
  | rightColdBoundary
  deriving DecidableEq, Fintype, Repr

/-- Literal material, geometry, and temperature labels in the raster. -/
inductive FigureLabel where
  | copper
  | steel
  | copperLength20cm
  | steelLength10cm
  | copperSide2cm
  | steelSide2cm
  | copperHot100C
  | copperCold0C
  | steelHot100C
  | steelCold0C
  deriving DecidableEq, Fintype, Repr

/-- Qualitative and label-level evidence read from the primary image. -/
structure SeparatedBarsFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  upperBar : Bar
  lowerBar : Bar
  barsTouchEachOther : Bool
  hotEndTouchesLeftBoundary : Bar → Bool
  coldEndTouchesRightBoundary : Bar → Bool
  lengthArrowLabel : Bar → FigureLabel
  sideArrowLabel : Bar → FigureLabel
  hotTemperatureLabel : Bar → FigureLabel
  coldTemperatureLabel : Bar → FigureLabel

/-! ## Independent setup and assumption interfaces -/

/-!
The total and per-bar heat currents are independent physical observables.  In
particular, `totalHeatCurrent` is not defined from `97.1 W`, from an answer
choice, or from the Fourier formula.
-/
structure SeparatedBarConductionSetup where
  barLength : Bar → LengthQuantity
  crossSectionSide : Bar → LengthQuantity
  crossSectionArea : Bar → AreaQuantity
  crossSectionShape : Bar → CrossSectionShape
  material : Bar → BarMaterial
  materialConductivity : BarMaterial → ThermalConductivityQuantity
  temperatureAt : Bar → BarEnd → CelsiusTemperatureReading
  barHeatCurrent : Bar → HeatCurrentQuantity
  totalHeatCurrent : HeatCurrentQuantity
  arrangement : BarArrangement
  regime : ThermalRegime
  figure : SeparatedBarsFigure

/-- Categorical scenario stated in the prose after the bars are separated. -/
structure MatchesSeparatedBarScenario
    (setup : SeparatedBarConductionSetup) : Prop where
  copperBarMaterial : setup.material .copperBar = .copper
  steelBarMaterial : setup.material .steelBar = .steel
  barsAreSeparated : setup.arrangement = .separatedParallelPaths
  conductionIsSteady : setup.regime = .steadyState
  bothCrossSectionsSquare :
    ∀ bar, setup.crossSectionShape bar = .square

/-- Detailed transcription of the labels and geometry in the primary raster. -/
structure MatchesSuppliedFigure
    (setup : SeparatedBarConductionSetup) : Prop where
  everyNamedObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everyPrintedLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  copperIsUpperBar : setup.figure.upperBar = .copperBar
  steelIsLowerBar : setup.figure.lowerBar = .steelBar
  visibleGapBetweenBars : setup.figure.barsTouchEachOther = false
  everyHotEndAtLeftBoundary :
    ∀ bar, setup.figure.hotEndTouchesLeftBoundary bar = true
  everyColdEndAtRightBoundary :
    ∀ bar, setup.figure.coldEndTouchesRightBoundary bar = true
  copperLengthLabel :
    setup.figure.lengthArrowLabel .copperBar = .copperLength20cm
  steelLengthLabel :
    setup.figure.lengthArrowLabel .steelBar = .steelLength10cm
  copperSideLabel :
    setup.figure.sideArrowLabel .copperBar = .copperSide2cm
  steelSideLabel :
    setup.figure.sideArrowLabel .steelBar = .steelSide2cm
  copperHotLabel :
    setup.figure.hotTemperatureLabel .copperBar = .copperHot100C
  copperColdLabel :
    setup.figure.coldTemperatureLabel .copperBar = .copperCold0C
  steelHotLabel :
    setup.figure.hotTemperatureLabel .steelBar = .steelHot100C
  steelColdLabel :
    setup.figure.coldTemperatureLabel .steelBar = .steelCold0C

/-- Numerical geometry and endpoint thermometer readouts stated by the problem
and printed in the figure.  It contains no heat-current value. -/
structure MatchesProblemReadouts
    (setup : SeparatedBarConductionSetup) : Prop where
  copperLengthCentimeters :
    lengthInCentimeters (setup.barLength .copperBar) = 20
  steelLengthCentimeters :
    lengthInCentimeters (setup.barLength .steelBar) = 10
  copperSideCentimeters :
    lengthInCentimeters (setup.crossSectionSide .copperBar) = 2
  steelSideCentimeters :
    lengthInCentimeters (setup.crossSectionSide .steelBar) = 2
  copperHotCelsius :
    (setup.temperatureAt .copperBar .hot).degreesCelsius = 100
  copperColdCelsius :
    (setup.temperatureAt .copperBar .cold).degreesCelsius = 0
  steelHotCelsius :
    (setup.temperatureAt .steelBar .hot).degreesCelsius = 100
  steelColdCelsius :
    (setup.temperatureAt .steelBar .cold).degreesCelsius = 0

/-- Euclidean area law for the square cross sections. -/
structure SatisfiesSquareCrossSectionGeometry
    (setup : SeparatedBarConductionSetup) : Prop where
  squareAreaForEachBar :
    ∀ bar,
      setup.crossSectionShape bar = .square →
        areaInSquareCentimeters (setup.crossSectionArea bar) =
          lengthInCentimeters (setup.crossSectionSide bar) ^ 2

/-!
The extracted prompt omits the material table needed for a numerical choice.
The recorded answer is obtained from the standard textbook values
`k_copper = 385 W/(m K)` and `k_steel = 50.2 W/(m K)`; they are exposed as a
separate material calibration rather than hidden in the target.
-/
structure UsesTextbookThermalConductivities
    (setup : SeparatedBarConductionSetup) : Prop where
  copperConductivity :
    thermalConductivityInWattsPerMeterKelvin
      (setup.materialConductivity .copper) = 385
  steelConductivity :
    thermalConductivityInWattsPerMeterKelvin
      (setup.materialConductivity .steel) = 251 / 5

/-- Positivity and hot-to-cold ordering of the physical parameters. -/
structure HasPhysicalSeparatedBarParameters
    (setup : SeparatedBarConductionSetup) : Prop where
  lengthsPositive :
    ∀ bar, 0 < lengthInMeters (setup.barLength bar)
  sideLengthsPositive :
    ∀ bar, 0 < lengthInMeters (setup.crossSectionSide bar)
  areasPositive :
    ∀ bar, 0 < areaInSquareMeters (setup.crossSectionArea bar)
  conductivitiesPositive :
    ∀ material,
      0 < thermalConductivityInWattsPerMeterKelvin
        (setup.materialConductivity material)
  barHeatCurrentsPositive :
    ∀ bar, 0 < heatCurrentInWatts (setup.barHeatCurrent bar)
  totalHeatCurrentPositive :
    0 < heatCurrentInWatts setup.totalHeatCurrent
  absoluteTemperaturesPositive :
    ∀ bar barEnd,
      0 < (setup.temperatureAt bar barEnd).absoluteTemperature.toReal
  hotEndsAboveColdEnds :
    ∀ bar,
      (setup.temperatureAt bar .hot).degreesCelsius >
        (setup.temperatureAt bar .cold).degreesCelsius

/-!
Steady one-dimensional Fourier conduction in each homogeneous bar:

`heat current = conductivity * area * temperature drop / length`.

This is a governing law over both independent paths and contains no numerical
total or answer-choice relation.
-/
structure SatisfiesSteadyOneDimensionalFourierLaw
    (setup : SeparatedBarConductionSetup) : Prop where
  fourierLawForEachBar :
    ∀ bar,
      heatCurrentInWatts (setup.barHeatCurrent bar) =
        thermalConductivityInWattsPerMeterKelvin
            (setup.materialConductivity (setup.material bar)) *
          areaInSquareMeters (setup.crossSectionArea bar) *
          ((setup.temperatureAt bar .hot).degreesCelsius -
            (setup.temperatureAt bar .cold).degreesCelsius) /
          lengthInMeters (setup.barLength bar)

/-!
For the two separated bars bridging the same reservoirs, total heat current is
the sum of the two simultaneous path currents.  This conservation/additivity
law does not prescribe the requested numerical value.
-/
structure SatisfiesParallelHeatCurrentAdditivity
    (setup : SeparatedBarConductionSetup) : Prop where
  totalIsSumOfBarCurrents :
    heatCurrentInWatts setup.totalHeatCurrent =
      heatCurrentInWatts (setup.barHeatCurrent .copperBar) +
        heatCurrentInWatts (setup.barHeatCurrent .steelBar)

/-! ## Derived currents and multiple-choice conclusion -/

/-- The two Fourier-law currents before they are added: `77 W` in copper and
`20.08 W` in steel. -/
theorem individualHeatCurrents_exact
    (setup : SeparatedBarConductionSetup)
    (hScenario : MatchesSeparatedBarScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : SatisfiesSquareCrossSectionGeometry setup)
    (hConductivity : UsesTextbookThermalConductivities setup)
    (hPhysical : HasPhysicalSeparatedBarParameters setup)
    (hFourier : SatisfiesSteadyOneDimensionalFourierLaw setup) :
    heatCurrentInWatts (setup.barHeatCurrent .copperBar) = 77 ∧
      heatCurrentInWatts (setup.barHeatCurrent .steelBar) = 502 / 25 := by
  let centimeterUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  let meterUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.meters}
  have hCentimeterScale :
      LengthUnit.centimeters / LengthUnit.meters = (1 / 100 : NNReal) := by
    rw [show LengthUnit.centimeters =
      LengthUnit.scale ((1 / 10 : ℝ) ^ 2) LengthUnit.meters from rfl]
    rw [LengthUnit.scale_div_self]
    apply NNReal.eq
    change ((1 / 10 : ℝ) ^ 2) = ((1 / 100 : NNReal) : ℝ)
    norm_num
  have hLengthScale :
      centimeterUnits.dimScale meterUnits L𝓭 = (1 / 100 : NNReal) := by
    simp only [centimeterUnits, meterUnits, UnitChoices.dimScale_apply]
    rw [hCentimeterScale]
    norm_num
  have hAreaScale :
      centimeterUnits.dimScale meterUnits (L𝓭 * L𝓭) =
        (1 / 10000 : NNReal) := by
    simp only [centimeterUnits, meterUnits, UnitChoices.dimScale_apply]
    rw [hCentimeterScale]
    norm_num
  have lengthMeters_eq_centimeters_div
      (length : LengthQuantity) :
      lengthInMeters length = lengthInCentimeters length / 100 := by
    have hUnits := length.2 centimeterUnits meterUnits
    simp only [WithDim.dim_apply] at hUnits
    rw [hLengthScale] at hUnits
    have hValues := congrArg
      (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) hUnits
    simpa [centimeterUnits, meterUnits, lengthInMeters,
      lengthInCentimeters, lengthReadout, NNReal.smul_def,
      div_eq_mul_inv, mul_comm] using hValues
  have areaMeters_eq_centimeters_div
      (area : AreaQuantity) :
      areaInSquareMeters area = areaInSquareCentimeters area / 10000 := by
    have hUnits := area.2 centimeterUnits meterUnits
    simp only [WithDim.dim_apply] at hUnits
    rw [hAreaScale] at hUnits
    have hValues := congrArg
      (fun x : WithDim (L𝓭 * L𝓭) NNReal => (x.val : ℝ)) hUnits
    simpa [centimeterUnits, meterUnits, areaInSquareMeters,
      areaInSquareCentimeters, areaReadout, NNReal.smul_def,
      div_eq_mul_inv, mul_comm] using hValues
  have hCopperLength :
      lengthInMeters (setup.barLength .copperBar) = 1 / 5 := by
    rw [lengthMeters_eq_centimeters_div,
      hReadouts.copperLengthCentimeters]
    norm_num
  have hSteelLength :
      lengthInMeters (setup.barLength .steelBar) = 1 / 10 := by
    rw [lengthMeters_eq_centimeters_div,
      hReadouts.steelLengthCentimeters]
    norm_num
  have hCopperAreaCentimeters :
      areaInSquareCentimeters (setup.crossSectionArea .copperBar) = 4 := by
    rw [hGeometry.squareAreaForEachBar .copperBar
      (hScenario.bothCrossSectionsSquare .copperBar)]
    rw [hReadouts.copperSideCentimeters]
    norm_num
  have hSteelAreaCentimeters :
      areaInSquareCentimeters (setup.crossSectionArea .steelBar) = 4 := by
    rw [hGeometry.squareAreaForEachBar .steelBar
      (hScenario.bothCrossSectionsSquare .steelBar)]
    rw [hReadouts.steelSideCentimeters]
    norm_num
  have hCopperArea :
      areaInSquareMeters (setup.crossSectionArea .copperBar) = 1 / 2500 := by
    rw [areaMeters_eq_centimeters_div, hCopperAreaCentimeters]
    norm_num
  have hSteelArea :
      areaInSquareMeters (setup.crossSectionArea .steelBar) = 1 / 2500 := by
    rw [areaMeters_eq_centimeters_div, hSteelAreaCentimeters]
    norm_num
  have hCopperCurrent := hFourier.fourierLawForEachBar .copperBar
  rw [hScenario.copperBarMaterial, hConductivity.copperConductivity,
    hCopperArea, hReadouts.copperHotCelsius,
    hReadouts.copperColdCelsius, hCopperLength] at hCopperCurrent
  norm_num at hCopperCurrent
  have hSteelCurrent := hFourier.fourierLawForEachBar .steelBar
  rw [hScenario.steelBarMaterial, hConductivity.steelConductivity,
    hSteelArea, hReadouts.steelHotCelsius,
    hReadouts.steelColdCelsius, hSteelLength] at hSteelCurrent
  norm_num at hSteelCurrent
  exact ⟨hCopperCurrent, hSteelCurrent⟩

/-- The exact total heat current is `97.08 W`. -/
theorem totalHeatCurrent_exact
    (setup : SeparatedBarConductionSetup)
    (hScenario : MatchesSeparatedBarScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : SatisfiesSquareCrossSectionGeometry setup)
    (hConductivity : UsesTextbookThermalConductivities setup)
    (hPhysical : HasPhysicalSeparatedBarParameters setup)
    (hFourier : SatisfiesSteadyOneDimensionalFourierLaw setup)
    (hAdditivity : SatisfiesParallelHeatCurrentAdditivity setup) :
    heatCurrentInWatts setup.totalHeatCurrent = 2427 / 25 := by
  have hCurrents := individualHeatCurrents_exact setup hScenario hReadouts
    hGeometry hConductivity hPhysical hFourier
  rw [hAdditivity.totalIsSumOfBarCurrents, hCurrents.1, hCurrents.2]
  norm_num

/-- Labels of the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Watt value printed beside each answer choice. -/
def displayedHeatCurrentInWatts : AnswerChoice → ℝ
  | .A => 491 / 5
  | .B => 971 / 10
  | .C => 969 / 10
  | .D => 476 / 5

/-- Dataset metadata recording that the supplied answer label is `B`. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement with a one-decimal-place watt display. -/
def RoundsToDisplayedTenthWatt
    (heatCurrent : HeatCurrentQuantity) (displayedWatts : ℝ) : Prop :=
  |heatCurrentInWatts heatCurrent - displayedWatts| < (1 / 20 : ℝ)

/-- The total physical heat current rounds to the display for a choice. -/
def MatchesAnswerChoice
    (setup : SeparatedBarConductionSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedTenthWatt setup.totalHeatCurrent
    (displayedHeatCurrentInWatts choice)

/-!
The exact sum `97.08 W` rounds to `97.1 W`; among the four displayed values,
this uniquely selects answer `B`.

This is the formal target corresponding to
`thm:physics:phyx_mini_0468:target`.
-/
theorem problem_phyx_mini_0468
    (setup : SeparatedBarConductionSetup)
    (hScenario : MatchesSeparatedBarScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : SatisfiesSquareCrossSectionGeometry setup)
    (hConductivity : UsesTextbookThermalConductivities setup)
    (hPhysical : HasPhysicalSeparatedBarParameters setup)
    (hFourier : SatisfiesSteadyOneDimensionalFourierLaw setup)
    (hAdditivity : SatisfiesParallelHeatCurrentAdditivity setup) :
    heatCurrentInWatts setup.totalHeatCurrent = 2427 / 25 ∧
      MatchesAnswerChoice setup .B ∧
        ∀ choice, MatchesAnswerChoice setup choice → choice = .B := by
  have hTotal := totalHeatCurrent_exact setup hScenario hFigure hReadouts
    hGeometry hConductivity hPhysical hFourier hAdditivity
  refine ⟨hTotal, ?_, ?_⟩
  · unfold MatchesAnswerChoice RoundsToDisplayedTenthWatt
    rw [hTotal]
    norm_num [displayedHeatCurrentInWatts]
  · intro choice hChoice
    cases choice <;>
      norm_num [MatchesAnswerChoice, RoundsToDisplayedTenthWatt,
        displayedHeatCurrentInWatts, hTotal] at hChoice <;>
      rfl

end PhyXMiniProblems.ProblemPhyXMini0468
