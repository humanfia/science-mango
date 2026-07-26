import Mathlib.Order.Filter.Extr
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0646

open Dimension

/-!
# Blackbody temperature matched to a firefly emission peak

The chapter asks for the temperature of an ideal blackbody whose radiation
peaks at the same frequency as the observed firefly emission.  Its auxiliary
caption describes a relative-intensity spectrum peaking somewhere above
`600 nm` and below the displayed `700 nm` endpoint.  Vacuum dispersion and
Wien's displacement law determine the blackbody temperature from that peak
wavelength by `T = b / λ`.

The bitmap stored at the cited source path is inconsistent with that caption:
it depicts a V-shaped graph of `|ψ(x)|²` against `x (fm)`, with endpoints at
`-4 fm` and `4 fm` and a height marked `a`.  The declarations below preserve
that primary-raster evidence in a separate structure.  It is deliberately not
used as evidence for the firefly peak.

Wavelength, position, frequency, speed, probability density, and Wien's
constant are represented by Physlib dimensionful quantities.  The blackbody
temperature uses Physlib's absolute `Temperature`.  Reals occur only at named
unit-readout boundaries, on dimensionless plot axes, and in approximate
reported values.  Because the primary raster supplies no spectral wavelength
and the answer strings are truncated, no numerical temperature choice is
asserted as the physically supported target.

Assumption/target split:

* `MatchesPrimaryRaster646` records only labels and geometry visible in the
  mismatched primary bitmap;
* `MatchesReportedFireflySpectrumCaption` records the separate, caption-based
  spectrum readout;
* `HasMeasuredFireflySpectrumPeak` states the empirical maximum property;
* `UsesStandardBlackbodyConstants` calibrates universal constants;
* `SatisfiesVacuumDispersionAndWienLaws` and `HasSamePeakFrequency` state the
  governing physics and the design requirement; and
* `problem_phyx_mini_0646` alone concludes the exact requested temperature
  relation, both with the physical Wien constant and with its standard SI
  calibration.
-/

/-! ## Dimensions, physical quantities, and coherent readouts -/

/-- Frequency has dimension inverse time. -/
def frequencyDimension : Dimension := T𝓭⁻¹

/-- Speed has dimension length per time. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- A one-dimensional probability density has dimension inverse length. -/
def probabilityDensityDimension : Dimension := L𝓭⁻¹

/-- Wien's wavelength displacement constant has dimension length-temperature. -/
def wienDisplacementConstantDimension : Dimension := L𝓭 * Θ𝓭

/-- A nonnegative physical wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical position, used for the primary raster's `x` coordinate. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim frequencyDimension NNReal)

/-- A nonnegative physical speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative one-dimensional probability density. -/
abbrev ProbabilityDensityQuantity : Type :=
  Dimensionful (WithDim probabilityDensityDimension NNReal)

/-- A physical value of Wien's wavelength displacement constant. -/
abbrev WienDisplacementConstantQuantity : Type :=
  Dimensionful (WithDim wienDisplacementConstantDimension NNReal)

/-- Read a nonnegative dimensionful quantity in a coherent unit system. -/
def nnrealQuantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a signed dimensionful quantity in a coherent unit system. -/
def realQuantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

/-- Read a wavelength in a selected length unit. -/
def wavelengthReadout
    (unit : LengthUnit) (wavelength : WavelengthQuantity) : ℝ :=
  nnrealQuantityReadout {UnitChoices.SI with length := unit} wavelength

/-- Read a wavelength in metres. -/
def wavelengthInMeters (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.meters wavelength

/-- Read a wavelength in nanometres. -/
def wavelengthInNanometers (wavelength : WavelengthQuantity) : ℝ :=
  wavelengthReadout LengthUnit.nanometers wavelength

/-- Read a signed position in femtometres. -/
def positionInFemtometers (position : PositionQuantity) : ℝ :=
  realQuantityReadout
    {UnitChoices.SI with length := LengthUnit.femtometers} position

/-- Read a frequency in coherent-SI hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  nnrealQuantityReadout UnitChoices.SI frequency

/-- Read a speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  nnrealQuantityReadout UnitChoices.SI speed

/-- Read a probability density in inverse femtometres. -/
def probabilityDensityInPerFemtometer
    (density : ProbabilityDensityQuantity) : ℝ :=
  nnrealQuantityReadout
    {UnitChoices.SI with length := LengthUnit.femtometers} density

/-- Read Wien's constant in coherent-SI metre-kelvins. -/
def wienConstantInMeterKelvins
    (constant : WienDisplacementConstantQuantity) : ℝ :=
  nnrealQuantityReadout UnitChoices.SI constant

/-!
Read a Physlib absolute temperature in kelvins.  `Temperature` stores a
nonnegative magnitude in an arbitrary zero-preserving temperature unit, so
the storage unit is retained explicitly.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Primary bitmap evidence -/

/-- The two axes visible in the primary bitmap. -/
inductive PrimaryRasterAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical roles of the two primary-raster axes. -/
inductive PrimaryRasterAxisRole where
  | positionInFemtometers
  | oneDimensionalProbabilityDensity
  deriving DecidableEq, Repr

/-- Qualitative shape of the green curve visible in image `646.png`. -/
inductive PrimaryRasterCurveGeometry where
  | piecewiseLinearVWithEndpointDrops
  deriving DecidableEq, Repr

/-!
Typed transcription of the actual primary bitmap.  The scale `a` is kept as a
physical inverse-length quantity, rather than as an untyped scalar.
-/
structure PrimaryRaster646 where
  axisRole : PrimaryRasterAxis → PrimaryRasterAxisRole
  axisLabel : PrimaryRasterAxis → String
  displayedHorizontalTicksInFemtometers : List ℝ
  leftBoundaryPosition : PositionQuantity
  centralVertexPosition : PositionQuantity
  rightBoundaryPosition : PositionQuantity
  densityScale : ProbabilityDensityQuantity
  densityScaleLabel : String
  displayedDensity : PositionQuantity → ProbabilityDensityQuantity
  curveGeometry : PrimaryRasterCurveGeometry

/-!
Labels, coordinates, and incidence data read directly from the primary raster.
This predicate makes no claim that the bitmap is a firefly spectrum.
-/
structure MatchesPrimaryRaster646 (figure : PrimaryRaster646) : Prop where
  horizontalAxisRole :
    figure.axisRole .horizontal = .positionInFemtometers
  verticalAxisRole :
    figure.axisRole .vertical = .oneDimensionalProbabilityDensity
  horizontalAxisLabel : figure.axisLabel .horizontal = "x (fm)"
  verticalAxisLabel : figure.axisLabel .vertical = "|ψ(x)|²"
  horizontalTicks :
    figure.displayedHorizontalTicksInFemtometers = [-4, -2, 0, 2, 4]
  leftBoundaryReadout : positionInFemtometers figure.leftBoundaryPosition = -4
  centralVertexReadout : positionInFemtometers figure.centralVertexPosition = 0
  rightBoundaryReadout : positionInFemtometers figure.rightBoundaryPosition = 4
  densityScaleIsMarkedA : figure.densityScaleLabel = "a"
  densityScaleIsPositive :
    0 < probabilityDensityInPerFemtometer figure.densityScale
  leftTopHasDensityA :
    probabilityDensityInPerFemtometer
        (figure.displayedDensity figure.leftBoundaryPosition) =
      probabilityDensityInPerFemtometer figure.densityScale
  centralVertexHasZeroDensity :
    probabilityDensityInPerFemtometer
        (figure.displayedDensity figure.centralVertexPosition) = 0
  rightTopHasDensityA :
    probabilityDensityInPerFemtometer
        (figure.displayedDensity figure.rightBoundaryPosition) =
      probabilityDensityInPerFemtometer figure.densityScale
  displayedCurveGeometry :
    figure.curveGeometry = .piecewiseLinearVWithEndpointDrops

/-! ## Reported firefly spectrum and independent physical setup -/

/-- The observed source and the ideal comparison emitter. -/
inductive EmitterKind where
  | firefly
  | idealBlackbody
  | other
  deriving DecidableEq, Repr

/-- The axes of the firefly spectrum described by the chapter's caption. -/
inductive SpectrumAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical or dimensionless role assigned to a reported spectrum axis. -/
inductive SpectrumAxisRole where
  | wavelengthInNanometers
  | relativeIntensity
  deriving DecidableEq, Repr

/-!
Plot metadata asserted by the auxiliary caption.  It is intentionally not
identified with `PrimaryRaster646`, because the actual bitmap has different
labels and physical content.
-/
structure ReportedFireflySpectrumCaption where
  axisRole : SpectrumAxis → SpectrumAxisRole
  axisLabel : SpectrumAxis → String
  wavelengthAxisMinimumInNanometers : ℝ
  wavelengthAxisMaximumInNanometers : ℝ
  wavelengthTickValuesInNanometers : List ℝ
  relativeIntensityAxisMinimum : ℝ
  relativeIntensityAxisMaximum : ℝ
  relativeIntensityTickValues : List ℝ
  approximatePeakWavelengthInNanometers : ℝ
  peakRelativeIntensity : ℝ
  curveIsLightYellowShaded : Bool
  curveHasOrangeOutline : Bool

/-!
The requested blackbody temperature is an independent physical field.  It is
not defined from `5000`, an answer label, the reported plot, or Wien's law.
-/
structure FireflyBlackbodyPeakSetup where
  observedEmitter : EmitterKind
  comparisonEmitter : EmitterKind
  fireflyRelativeIntensity : WavelengthQuantity → NNReal
  fireflyPeakWavelength : WavelengthQuantity
  fireflyPeakFrequency : FrequencyQuantity
  blackbodyPeakWavelength : WavelengthQuantity
  blackbodyPeakFrequency : FrequencyQuantity
  blackbodyTemperatureStorageUnit : TemperatureUnit
  blackbodyTemperature : Temperature
  vacuumLightSpeed : SpeedQuantity
  wienDisplacementConstant : WienDisplacementConstantQuantity
  reportedSpectrumCaption : ReportedFireflySpectrumCaption
  primaryRaster : PrimaryRaster646

/-! ## Scenario data, calibrations, and governing laws -/

/-- Qualitative emitter roles stated in the problem. -/
structure MatchesFireflyBlackbodyScenario
    (setup : FireflyBlackbodyPeakSetup) : Prop where
  observedSourceIsFirefly : setup.observedEmitter = .firefly
  comparisonSourceIsIdealBlackbody :
    setup.comparisonEmitter = .idealBlackbody

/-!
Axis labels, ticks, colors, and approximate peak data asserted by the chapter
caption.  The peak is placed only between the stated `600 nm` tick and the
displayed `700 nm` endpoint.  No sharper tolerance is invented from the word
“slightly.”
-/
structure MatchesReportedFireflySpectrumCaption
    (setup : FireflyBlackbodyPeakSetup) : Prop where
  horizontalAxisRole :
    setup.reportedSpectrumCaption.axisRole .horizontal =
      .wavelengthInNanometers
  verticalAxisRole :
    setup.reportedSpectrumCaption.axisRole .vertical = .relativeIntensity
  horizontalAxisLabel :
    setup.reportedSpectrumCaption.axisLabel .horizontal = "Wavelength (nm)"
  verticalAxisLabel :
    setup.reportedSpectrumCaption.axisLabel .vertical = "Relative intensity"
  wavelengthAxisMinimum :
    setup.reportedSpectrumCaption.wavelengthAxisMinimumInNanometers = 300
  wavelengthAxisMaximum :
    setup.reportedSpectrumCaption.wavelengthAxisMaximumInNanometers = 700
  wavelengthTicks :
    setup.reportedSpectrumCaption.wavelengthTickValuesInNanometers =
      [400, 500, 600, 700]
  relativeIntensityAxisMinimum :
    setup.reportedSpectrumCaption.relativeIntensityAxisMinimum = 0
  relativeIntensityAxisMaximum :
    setup.reportedSpectrumCaption.relativeIntensityAxisMaximum = 1
  relativeIntensityTicks :
    setup.reportedSpectrumCaption.relativeIntensityTickValues =
      [0, 1 / 5, 2 / 5, 3 / 5, 4 / 5, 1]
  peakBetweenSixHundredAndSevenHundredNanometers :
    600 <
        setup.reportedSpectrumCaption.approximatePeakWavelengthInNanometers ∧
      setup.reportedSpectrumCaption.approximatePeakWavelengthInNanometers < 700
  physicalPeakAgreesWithCaptionReadout :
    wavelengthInNanometers setup.fireflyPeakWavelength =
      setup.reportedSpectrumCaption.approximatePeakWavelengthInNanometers
  peakRelativeIntensityIsOne :
    setup.reportedSpectrumCaption.peakRelativeIntensity = 1
  physicalPeakHasUnitRelativeIntensity :
    (setup.fireflyRelativeIntensity setup.fireflyPeakWavelength : ℝ) = 1
  curveIsShaded :
    setup.reportedSpectrumCaption.curveIsLightYellowShaded = true
  curveOutlineIsOrange :
    setup.reportedSpectrumCaption.curveHasOrangeOutline = true

/-!
The measured firefly wavelength is a global maximum of the dimensionless
relative-intensity spectrum.  Mathlib's `IsMaxOn` supplies the exact maximum
predicate.
-/
structure HasMeasuredFireflySpectrumPeak
    (setup : FireflyBlackbodyPeakSetup) : Prop where
  relativeIntensityAtMostOne : ∀ wavelength,
    (setup.fireflyRelativeIntensity wavelength : ℝ) ≤ 1
  measuredWavelengthIsGlobalPeak :
    IsMaxOn
      (fun wavelength => (setup.fireflyRelativeIntensity wavelength : ℝ))
      Set.univ setup.fireflyPeakWavelength

/-- Positivity and nondegeneracy conditions for the physical quantities. -/
structure HasPhysicalPeakMatchingParameters
    (setup : FireflyBlackbodyPeakSetup) : Prop where
  positiveFireflyPeakWavelength :
    0 < wavelengthInMeters setup.fireflyPeakWavelength
  positiveFireflyPeakFrequency :
    0 < frequencyInHertz setup.fireflyPeakFrequency
  positiveBlackbodyPeakWavelength :
    0 < wavelengthInMeters setup.blackbodyPeakWavelength
  positiveBlackbodyPeakFrequency :
    0 < frequencyInHertz setup.blackbodyPeakFrequency
  positiveBlackbodyTemperature :
    0 < temperatureInKelvins setup.blackbodyTemperatureStorageUnit
      setup.blackbodyTemperature
  positiveVacuumLightSpeed :
    0 < speedInMetersPerSecond setup.vacuumLightSpeed
  positiveWienConstant :
    0 < wienConstantInMeterKelvins setup.wienDisplacementConstant

/-!
Standard coherent-SI calibrations.  They are universal physical constants,
not fitted values of the requested temperature.
-/
structure UsesStandardBlackbodyConstants
    (setup : FireflyBlackbodyPeakSetup) : Prop where
  vacuumLightSpeedSI :
    speedInMetersPerSecond setup.vacuumLightSpeed = 299792458
  wienDisplacementConstantSI :
    wienConstantInMeterKelvins setup.wienDisplacementConstant =
      2898 / 1000000

/-!
Vacuum dispersion `c = λν` for both emission peaks and Wien's wavelength
displacement law `λ_max T = b` for the ideal blackbody.  No rounded
temperature conclusion occurs in these governing relations.
-/
structure SatisfiesVacuumDispersionAndWienLaws
    (setup : FireflyBlackbodyPeakSetup) : Prop where
  fireflyPeakDispersion :
    wavelengthInMeters setup.fireflyPeakWavelength *
        frequencyInHertz setup.fireflyPeakFrequency =
      speedInMetersPerSecond setup.vacuumLightSpeed
  blackbodyPeakDispersion :
    wavelengthInMeters setup.blackbodyPeakWavelength *
        frequencyInHertz setup.blackbodyPeakFrequency =
      speedInMetersPerSecond setup.vacuumLightSpeed
  wienDisplacementLaw :
    wavelengthInMeters setup.blackbodyPeakWavelength *
        temperatureInKelvins setup.blackbodyTemperatureStorageUnit
          setup.blackbodyTemperature =
      wienConstantInMeterKelvins setup.wienDisplacementConstant

/-!
The design condition from the question: the ideal blackbody is chosen to peak
at the same physical frequency as the firefly.
-/
structure HasSamePeakFrequency
    (setup : FireflyBlackbodyPeakSetup) : Prop where
  samePeakFrequency :
    setup.blackbodyPeakFrequency = setup.fireflyPeakFrequency

/-! ## Derived relations and requested temperature -/

/-- Equal positive peak frequencies under `c = λν` give equal wavelengths. -/
lemma matched_peak_wavelengths_equal
    (setup : FireflyBlackbodyPeakSetup)
    (h_physical : HasPhysicalPeakMatchingParameters setup)
    (h_laws : SatisfiesVacuumDispersionAndWienLaws setup)
    (h_sameFrequency : HasSamePeakFrequency setup) :
    wavelengthInMeters setup.blackbodyPeakWavelength =
      wavelengthInMeters setup.fireflyPeakWavelength := by
  have h_blackbody := h_laws.blackbodyPeakDispersion
  rw [h_sameFrequency.samePeakFrequency] at h_blackbody
  nlinarith [h_laws.fireflyPeakDispersion,
    h_physical.positiveFireflyPeakFrequency]

/-!
The exact, unrounded temperature relation obtained after eliminating the
blackbody peak wavelength.
-/
lemma matched_peak_wien_relation
    (setup : FireflyBlackbodyPeakSetup)
    (h_physical : HasPhysicalPeakMatchingParameters setup)
    (h_laws : SatisfiesVacuumDispersionAndWienLaws setup)
    (h_sameFrequency : HasSamePeakFrequency setup) :
    wavelengthInMeters setup.fireflyPeakWavelength *
        temperatureInKelvins setup.blackbodyTemperatureStorageUnit
          setup.blackbodyTemperature =
      wienConstantInMeterKelvins setup.wienDisplacementConstant := by
  rw [← matched_peak_wavelengths_equal setup h_physical h_laws
    h_sameFrequency]
  exact h_laws.wienDisplacementLaw

/-- Labels retained from the truncated multiple-choice source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The source metadata records label C; this value is not used as a premise. -/
def recordedAnswerLabel : AnswerChoice := .C

/-!
The equal-frequency design condition and the two vacuum-dispersion relations
identify the firefly and blackbody peak wavelengths.  Wien's displacement law
then determines the requested absolute temperature as `b / λ_firefly`.

The second conjunct specializes `b` to `2898 / 1000000 m K`.  The source's
option strings are truncated and the actual primary raster contains no
wavelength scale, so this theorem does not invent a numerical choice or a
rounding tolerance from the auxiliary caption.

This declaration corresponds to
`thm:physics:phyx_mini_0646:target`.
-/
theorem problem_phyx_mini_0646
    (setup : FireflyBlackbodyPeakSetup)
    (h_scenario : MatchesFireflyBlackbodyScenario setup)
    (h_primaryFigure : MatchesPrimaryRaster646 setup.primaryRaster)
    (h_caption : MatchesReportedFireflySpectrumCaption setup)
    (h_peak : HasMeasuredFireflySpectrumPeak setup)
    (h_physical : HasPhysicalPeakMatchingParameters setup)
    (h_constants : UsesStandardBlackbodyConstants setup)
    (h_laws : SatisfiesVacuumDispersionAndWienLaws setup)
    (h_sameFrequency : HasSamePeakFrequency setup) :
    temperatureInKelvins setup.blackbodyTemperatureStorageUnit
          setup.blackbodyTemperature =
        wienConstantInMeterKelvins setup.wienDisplacementConstant /
          wavelengthInMeters setup.fireflyPeakWavelength ∧
      temperatureInKelvins setup.blackbodyTemperatureStorageUnit
          setup.blackbodyTemperature =
        (2898 / 1000000) /
          wavelengthInMeters setup.fireflyPeakWavelength := by
  have h_wavelength_ne :
      wavelengthInMeters setup.fireflyPeakWavelength ≠ 0 :=
    ne_of_gt h_physical.positiveFireflyPeakWavelength
  have h_wien := matched_peak_wien_relation setup h_physical h_laws
    h_sameFrequency
  constructor
  · apply (eq_div_iff h_wavelength_ne).2
    simpa [mul_comm] using h_wien
  · rw [← h_constants.wienDisplacementConstantSI]
    apply (eq_div_iff h_wavelength_ne).2
    simpa [mul_comm] using h_wien

end PhyXMiniProblems.ProblemPhyXMini0646
