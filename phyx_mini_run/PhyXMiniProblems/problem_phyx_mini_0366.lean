import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0366

open Dimension

/-!
# Mercury compression of air in a U-shaped tube

The tube has uniform cross-section and total centre-line length `1.0 m`.  Its
left end is open to the atmosphere and its right end is sealed.  Initially the
whole tube contains air at `20 °C` and `1 atm`.  Mercury is poured slowly into
the open end without loss of trapped air.  In the final configuration shown in
the supplied raster, `L` is the vertical distance from the open top to the
mercury--air interface.

Lengths, areas, volumes, pressures, mass density, acceleration, and absolute
temperature remain physical quantities.  Real numbers below are explicitly
named SI or centimetre readouts, qualitative schematic coordinates, or
dimensionless answer-choice values.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative physical volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- A nonnegative mass density, with dimension mass per volume. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical area in SI square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical mass density in kilograms per cubic metre. -/
def massDensityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Kelvin readout of Physlib's absolute-temperature object. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- Celsius readout relative to the conventional `273.15 K` offset. -/
def temperatureInCelsius (temperature : Temperature) : ℝ :=
  temperatureInKelvins temperature - 27315 / 100

/-! ## Physical roles and primary-figure labels -/

/-- Thermodynamic model used for the trapped air. -/
inductive GasModel where
  | idealGas
  deriving DecidableEq, Repr

/-- Material names appearing in the problem and primary figure. -/
inductive Substance where
  | mercury
  | air
  deriving DecidableEq, Repr

/-- Boundary condition at either end of the U-tube. -/
inductive EndBoundary where
  | openToAtmosphere
  | sealedClosed
  deriving DecidableEq, Repr

/-- The two explicitly labelled ends of the tube. -/
inductive TubeEnd where
  | openEnd
  | closedEnd
  deriving DecidableEq, Repr

/-- Regions distinguished by the material labels in the final figure. -/
inductive FigureRegion where
  | openLegColumn
  | remainingTube
  deriving DecidableEq, Repr

/-- Distinguished endpoints of the arrow marked `L`. -/
inductive FigurePoint where
  | mercuryAirInterface
  | openTop
  | closedTop
  deriving DecidableEq, Repr

/-- The literal length symbol printed in the supplied raster. -/
inductive FigureLengthLabel where
  | L
  deriving DecidableEq, Repr

/-- Direction of the double-ended length marker in the raster. -/
inductive FigureArrowDirection where
  | vertical
  deriving DecidableEq, Repr

/-- Slow-pouring and containment information from the prose scenario. -/
inductive CompressionRegime where
  | slowlyQuasistatic
  deriving DecidableEq, Repr

/-- Whether the initially trapped sample can escape during compression. -/
inductive AirContainment where
  | noAirEscapes
  deriving DecidableEq, Repr

/--
Qualitative transcription of the supplied U-tube image.  The physical length
represented by the arrow is stored independently of its later numerical
solution.
-/
structure UTubeFigure where
  boundaryAt : TubeEnd → EndBoundary
  substanceIn : FigureRegion → Substance
  lengthLabel : FigureLengthLabel
  lengthArrowStart : FigurePoint
  lengthArrowEnd : FigurePoint
  lengthArrowDirection : FigureArrowDirection
  representedLength : LengthQuantity
  substanceLabelVisible : Substance → Bool
  endLabelVisible : TubeEnd → Bool
  schematicVerticalCoordinate : FigurePoint → ℝ

/-!
Independent physical quantities for the initial and final equilibrium states.
In particular, `mercuryColumnLength` is a field, not a definition of the
requested `24 cm` result.
-/
structure UTubeCompressionSetup where
  gasModel : GasModel
  pouredLiquid : Substance
  regime : CompressionRegime
  airContainment : AirContainment
  tubeTotalLength : LengthQuantity
  uniformCrossSectionalArea : AreaQuantity
  mercuryColumnLength : LengthQuantity
  initialTrappedAirVolume : VolumeQuantity
  finalTrappedAirVolume : VolumeQuantity
  ambientPressure : PressureQuantity
  initialTrappedAirPressure : PressureQuantity
  finalTrappedAirPressure : PressureQuantity
  initialAirTemperature : Temperature
  finalAirTemperature : Temperature
  mercuryMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  /-- Mercury height whose hydrostatic pressure equals the ambient atmosphere. -/
  atmosphericEquivalentMercuryHead : LengthQuantity
  figure : UTubeFigure

/-! ## Stated data, figure evidence, and governing laws -/

/-- Numerical and qualitative data stated in the problem text. -/
structure MatchesStatedProblemData (setup : UTubeCompressionSetup) : Prop where
  airIsIdeal : setup.gasModel = .idealGas
  pouredLiquidIsMercury : setup.pouredLiquid = .mercury
  pouringIsSlow : setup.regime = .slowlyQuasistatic
  fixedTrappedSample : setup.airContainment = .noAirEscapes
  totalTubeLengthMeters : lengthInMeters setup.tubeTotalLength = 1
  ambientIsOneStandardAtmosphere :
    setup.ambientPressure = DimPressure.standardAtmosphere
  initialAirPressureIsAmbient :
    setup.initialTrappedAirPressure = setup.ambientPressure
  initialAirTemperatureCelsius :
    temperatureInCelsius setup.initialAirTemperature = 20

/-!
Primary-image evidence: the left end is open, the right end is closed, mercury
occupies the open-leg column, and the arrow `L` runs vertically from the
mercury--air interface to the open top.
-/
structure MatchesPrimaryUTubeFigure (setup : UTubeCompressionSetup) : Prop where
  openEndBoundary :
    setup.figure.boundaryAt .openEnd = .openToAtmosphere
  closedEndBoundary :
    setup.figure.boundaryAt .closedEnd = .sealedClosed
  openLegContainsMercury :
    setup.figure.substanceIn .openLegColumn = .mercury
  remainingTubeContainsAir :
    setup.figure.substanceIn .remainingTube = .air
  displayedLengthLabel : setup.figure.lengthLabel = .L
  arrowStartsAtInterface :
    setup.figure.lengthArrowStart = .mercuryAirInterface
  arrowEndsAtOpenTop : setup.figure.lengthArrowEnd = .openTop
  arrowIsVertical : setup.figure.lengthArrowDirection = .vertical
  arrowRepresentsMercuryColumnLength :
    setup.figure.representedLength = setup.mercuryColumnLength
  mercuryLabelShown : setup.figure.substanceLabelVisible .mercury = true
  airLabelShown : setup.figure.substanceLabelVisible .air = true
  openLabelShown : setup.figure.endLabelVisible .openEnd = true
  closedLabelShown : setup.figure.endLabelVisible .closedEnd = true
  interfaceBelowOpenTop :
    setup.figure.schematicVerticalCoordinate .mercuryAirInterface <
      setup.figure.schematicVerticalCoordinate .openTop

/-!
School-level pressure calibration used by the answer choices: one atmosphere
supports a mercury column of `76 cm`.  This is reference data, not the unknown
mercury length `L`.
-/
structure UsesAtmosphericMercuryCalibration
    (setup : UTubeCompressionSetup) : Prop where
  oneAtmosphereHeadCentimeters :
    lengthInCentimeters setup.atmosphericEquivalentMercuryHead = 76

/-- Positivity and containment conditions selecting the physical, nonzero branch. -/
structure HasPhysicalUTubeParameters (setup : UTubeCompressionSetup) : Prop where
  crossSectionPositive :
    0 < areaInSquareMeters setup.uniformCrossSectionalArea
  mercuryDensityPositive :
    0 < massDensityInKilogramsPerCubicMeter setup.mercuryMassDensity
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  ambientPressurePositive :
    0 < pressureInPascals setup.ambientPressure
  initialAirVolumePositive :
    0 < volumeInCubicMeters setup.initialTrappedAirVolume
  finalAirVolumePositive :
    0 < volumeInCubicMeters setup.finalTrappedAirVolume
  mercuryWasActuallyPoured :
    0 < lengthInMeters setup.mercuryColumnLength
  mercuryColumnFitsTube :
    lengthInMeters setup.mercuryColumnLength <
      lengthInMeters setup.tubeTotalLength

/-!
Uniform-cross-section geometry.  Initially the air occupies the whole tube;
finally it occupies the remaining centre-line length after the vertical
mercury column of length `L` is filled.
-/
structure SatisfiesUniformTubeGeometry
    (setup : UTubeCompressionSetup) : Prop where
  initialAirFillsWholeTube :
    volumeInCubicMeters setup.initialTrappedAirVolume =
      areaInSquareMeters setup.uniformCrossSectionalArea *
        lengthInMeters setup.tubeTotalLength
  finalAirOccupiesRemainder :
    volumeInCubicMeters setup.finalTrappedAirVolume =
      areaInSquareMeters setup.uniformCrossSectionalArea *
        (lengthInMeters setup.tubeTotalLength -
          lengthInMeters setup.mercuryColumnLength)

/-!
Fixed-sample isothermal ideal-gas law.  Slow compression keeps the trapped air
at its initial temperature, and Boyle's product `pV` is therefore conserved.
-/
structure SatisfiesIsothermalFixedSampleIdealGasLaw
    (setup : UTubeCompressionSetup) : Prop where
  temperatureRemainsConstant :
    setup.finalAirTemperature = setup.initialAirTemperature
  boyleLaw :
    pressureInPascals setup.initialTrappedAirPressure *
        volumeInCubicMeters setup.initialTrappedAirVolume =
      pressureInPascals setup.finalTrappedAirPressure *
        volumeInCubicMeters setup.finalTrappedAirVolume

/-!
Hydrostatic equilibrium for mercury.  The first relation defines the
atmosphere-equivalent mercury head; the second gives the pressure increase at
the lower mercury--air interface.  Both are general `Δp = ρ g h` relations
and neither prescribes the requested column length.
-/
structure SatisfiesMercuryHydrostaticEquilibrium
    (setup : UTubeCompressionSetup) : Prop where
  atmosphereSupportedByReferenceHead :
    pressureInPascals setup.ambientPressure =
      massDensityInKilogramsPerCubicMeter setup.mercuryMassDensity *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          lengthInMeters setup.atmosphericEquivalentMercuryHead
  compressedAirPressureAtInterface :
    pressureInPascals setup.finalTrappedAirPressure =
      pressureInPascals setup.ambientPressure +
        massDensityInKilogramsPerCubicMeter setup.mercuryMassDensity *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
            lengthInMeters setup.mercuryColumnLength

/-! ## Requested mercury-column length -/

/-- Labels of the four answer choices displayed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Centimetre value printed beside each displayed answer label. -/
def displayedLengthCentimeters : AnswerChoice → ℝ
  | .A => 24
  | .B => 22
  | .C => 20
  | .D => 21

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
The physical laws first determine the exact SI length
`L = 0.24 m = 6/25 m`.
-/
lemma mercuryColumnLengthInMeters
    (setup : UTubeCompressionSetup)
    (h_data : MatchesStatedProblemData setup)
    (h_calibration : UsesAtmosphericMercuryCalibration setup)
    (h_physical : HasPhysicalUTubeParameters setup)
    (h_geometry : SatisfiesUniformTubeGeometry setup)
    (h_gas : SatisfiesIsothermalFixedSampleIdealGasLaw setup)
    (h_hydrostatic : SatisfiesMercuryHydrostaticEquilibrium setup) :
    lengthInMeters setup.mercuryColumnLength = 6 / 25 := by
  have h_head :
      lengthInMeters setup.atmosphericEquivalentMercuryHead = 19 / 25 := by
    have h := h_calibration.oneAtmosphereHeadCentimeters
    rw [lengthInCentimeters] at h
    norm_num at h ⊢
    linarith
  have h_boyle := h_gas.boyleLaw
  rw [h_data.initialAirPressureIsAmbient,
      h_geometry.initialAirFillsWholeTube,
      h_geometry.finalAirOccupiesRemainder,
      h_hydrostatic.compressedAirPressureAtInterface,
      h_data.totalTubeLengthMeters] at h_boyle
  have h_atmos := h_hydrostatic.atmosphereSupportedByReferenceHead
  rw [h_head] at h_atmos
  rw [h_atmos] at h_boyle
  have h_factor :
      (areaInSquareMeters setup.uniformCrossSectionalArea *
        massDensityInKilogramsPerCubicMeter setup.mercuryMassDensity *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        lengthInMeters setup.mercuryColumnLength) *
          (6 / 25 - lengthInMeters setup.mercuryColumnLength) = 0 := by
    nlinarith [h_boyle]
  have h_positive :
      0 < areaInSquareMeters setup.uniformCrossSectionalArea *
        massDensityInKilogramsPerCubicMeter setup.mercuryMassDensity *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        lengthInMeters setup.mercuryColumnLength := by
    exact mul_pos
      (mul_pos
        (mul_pos h_physical.crossSectionPositive h_physical.mercuryDensityPositive)
        h_physical.gravitationalAccelerationPositive)
      h_physical.mercuryWasActuallyPoured
  have h_root :=
    (mul_eq_zero.mp h_factor).resolve_left (ne_of_gt h_positive)
  linarith

/-!
Consequently the mercury column has length `24 cm`, selecting displayed and
recorded answer A.

Blueprint: `thm:physics:phyx_mini_0366:target`.
-/
theorem problem_phyx_mini_0366
    (setup : UTubeCompressionSetup)
    (h_data : MatchesStatedProblemData setup)
    (h_figure : MatchesPrimaryUTubeFigure setup)
    (h_calibration : UsesAtmosphericMercuryCalibration setup)
    (h_physical : HasPhysicalUTubeParameters setup)
    (h_geometry : SatisfiesUniformTubeGeometry setup)
    (h_gas : SatisfiesIsothermalFixedSampleIdealGasLaw setup)
    (h_hydrostatic : SatisfiesMercuryHydrostaticEquilibrium setup) :
    lengthInMeters setup.mercuryColumnLength = 6 / 25 ∧
      lengthInCentimeters setup.mercuryColumnLength = 24 ∧
      lengthInCentimeters setup.mercuryColumnLength =
        displayedLengthCentimeters recordedAnswerChoice := by
  have h_meters := mercuryColumnLengthInMeters setup h_data h_calibration h_physical
    h_geometry h_gas h_hydrostatic
  constructor
  · exact h_meters
  constructor
  · rw [lengthInCentimeters, h_meters]
    norm_num
  · rw [lengthInCentimeters, h_meters]
    norm_num [displayedLengthCentimeters, recordedAnswerChoice]

end PhyXMiniProblems.ProblemPhyXMini0366
