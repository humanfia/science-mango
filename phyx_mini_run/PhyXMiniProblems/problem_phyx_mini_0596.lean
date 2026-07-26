import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0596

open Dimension

/-!
# Radial speed of NGC 7319 from its optical redshift

The strongest oxygen emission line has laboratory wavelength `513 nm` and is
observed from Earth at `525 nm`.  The supplied spectrum marks the positive
shift `Δλ = +12 nm`.  In the low-speed optical Doppler model,

`(λ_observed - λ_laboratory) / λ_laboratory ≈ v_radial / c`.

The approximation is formalized below by a derivative at rest together with a
quadratic remainder estimate on an explicit low-speed neighborhood.

Lengths and speeds below are unit-independent Physlib quantities.  Real
numbers are used only for named unit readouts, dimensionless ratios, the
graph's scalar intensity readout, and displayed answer values.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Nanometre readout of a wavelength. -/
def wavelengthInNanometers (wavelength : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers wavelength

/-- Light-year readout of an astronomical distance. -/
def distanceInLightYears (distance : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.lightYears distance

/-- Metres-per-second readout of a nonnegative physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum light speed, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Source, spectrum, observer, and primary-figure vocabulary -/

/-- The emitting galaxy named in the problem and image. -/
inductive GalaxyLabel where
  | NGC7319
  deriving DecidableEq, Repr

/-- The two inertial-frame roles needed for the radial measurement. -/
inductive ReferenceFrame where
  | earthObserver
  | galaxyRest
  deriving DecidableEq, Repr

/-- Whether the source is approaching or receding along the line of sight. -/
inductive RadialDirection where
  | approaching
  | receding
  deriving DecidableEq, Repr

/-- Chemical species explicitly identified as producing the strongest line. -/
inductive EmittingSpecies where
  | oxygen
  | other
  deriving DecidableEq, Repr

/-- The two labeled coordinate axes of the supplied spectrum. -/
inductive SpectrumAxisLabel where
  | wavelengthNanometers
  | intensity
  deriving DecidableEq, Repr

/-- The green trace color visible in the primary image. -/
inductive SpectrumTraceColor where
  | green
  deriving DecidableEq, Repr

/-!
Literal and qualitative evidence from `phyx_data/test_image/596.png`.
Intensity numbers are scalar graph readouts because the vertical axis supplies
no physical unit.  This structure contains no radial-speed value or answer
choice.
-/
structure GalaxySpectrumFigure where
  horizontalAxisLabel : SpectrumAxisLabel
  verticalAxisLabel : SpectrumAxisLabel
  wavelengthAxisLowerNanometers : ℝ
  wavelengthAxisUpperNanometers : ℝ
  lowestLabeledIntensity : ℝ
  highestLabeledIntensity : ℝ
  intensityAxisBreakShown : Bool
  traceColor : SpectrumTraceColor
  galaxyLabel : GalaxyLabel
  laboratoryWavelengthMarkerShown : Bool
  positiveShiftArrowShown : Bool
  shiftAnnotationNanometers : ℝ

/-!
The physical spectrum and the requested observable.  `SpectralLine` is kept
abstract so that the statement that all emissions are redshifted can be
expressed without pretending that a spectrum has only the oxygen peak.
The plotted intensity is explicitly a scalar readout rather than a scalar
replacement for a physical intensity quantity.
-/
structure GalaxyRedshiftSetup (SpectralLine : Type) where
  figure : GalaxySpectrumFigure
  galaxy : GalaxyLabel
  sourceFrame : ReferenceFrame
  observerFrame : ReferenceFrame
  sourceEarthDistance : LengthQuantity
  oxygenLine : SpectralLine
  emittingSpecies : SpectralLine → EmittingSpecies
  laboratoryWavelength : SpectralLine → LengthQuantity
  earthObservedWavelength : SpectralLine → LengthQuantity
  plottedIntensityReadout : SpectralLine → ℝ
  radialDirectionRelativeToEarth : RadialDirection
  radialSpeedRelativeToEarth : SpeedQuantity

/-! ## Scenario, figure evidence, and supplied readouts -/

/--
Object, frame, emitting-species, dominance, and common-redshift information
stated in the prose.  The unknown speed is given only its physical role and
direction, not a numerical value.
-/
structure MatchesNGC7319SpectrumScenario
    {SpectralLine : Type} (setup : GalaxyRedshiftSetup SpectralLine) : Prop where
  namedGalaxy : setup.galaxy = .NGC7319
  sourceUsesGalaxyRestFrame : setup.sourceFrame = .galaxyRest
  observationMadeInEarthFrame : setup.observerFrame = .earthObserver
  oxygenProducesNamedLine :
    setup.emittingSpecies setup.oxygenLine = .oxygen
  oxygenLineIsMostIntense : ∀ line, line ≠ setup.oxygenLine →
    setup.plottedIntensityReadout line <
      setup.plottedIntensityReadout setup.oxygenLine
  everyPlottedIntensityNonnegative : ∀ line,
    0 ≤ setup.plottedIntensityReadout line
  everyEmissionIsRedshifted : ∀ line,
    wavelengthInNanometers (setup.laboratoryWavelength line) <
      wavelengthInNanometers (setup.earthObservedWavelength line)
  galaxyIsReceding : setup.radialDirectionRelativeToEarth = .receding

/-- Salient labels, bounds, color, and annotation visible in the raster. -/
structure MatchesPrimarySpectrumFigure
    {SpectralLine : Type} (setup : GalaxyRedshiftSetup SpectralLine) : Prop where
  horizontalAxisIsWavelength :
    setup.figure.horizontalAxisLabel = .wavelengthNanometers
  verticalAxisIsIntensity :
    setup.figure.verticalAxisLabel = .intensity
  wavelengthAxisStartsAt400 :
    setup.figure.wavelengthAxisLowerNanometers = 400
  wavelengthAxisEndsAt750 :
    setup.figure.wavelengthAxisUpperNanometers = 750
  lowestIntensityTickIsZero :
    setup.figure.lowestLabeledIntensity = 0
  highestIntensityTickIs800 :
    setup.figure.highestLabeledIntensity = 800
  intensityAxisHasBreak : setup.figure.intensityAxisBreakShown = true
  spectrumTraceIsGreen : setup.figure.traceColor = .green
  imageNamesNGC7319 : setup.figure.galaxyLabel = .NGC7319
  laboratoryMarkerIsShown :
    setup.figure.laboratoryWavelengthMarkerShown = true
  positiveShiftArrowIsShown : setup.figure.positiveShiftArrowShown = true
  imageShiftLabelNanometers : setup.figure.shiftAnnotationNanometers = 12

/-!
The numerical data supplied in the problem and its figure: distance
`3 × 10^8 ly`, laboratory oxygen wavelength `513 nm`, observed oxygen
wavelength `525 nm`, and their `+12 nm` difference.  No speed occurs here.
-/
structure MatchesNGC7319ProblemReadouts
    {SpectralLine : Type} (setup : GalaxyRedshiftSetup SpectralLine) : Prop where
  distanceLightYears :
    distanceInLightYears setup.sourceEarthDistance = 300000000
  laboratoryOxygenWavelengthNanometers :
    wavelengthInNanometers
        (setup.laboratoryWavelength setup.oxygenLine) = 513
  observedOxygenWavelengthNanometers :
    wavelengthInNanometers
        (setup.earthObservedWavelength setup.oxygenLine) = 525
  oxygenShiftMatchesFigure :
    wavelengthInNanometers
          (setup.earthObservedWavelength setup.oxygenLine) -
        wavelengthInNanometers
          (setup.laboratoryWavelength setup.oxygenLine) =
      setup.figure.shiftAnnotationNanometers

/-- Positivity conditions needed for wavelength ratios and the physical speed. -/
structure HasPhysicalRedshiftParameters
    {SpectralLine : Type} (setup : GalaxyRedshiftSetup SpectralLine) : Prop where
  sourceDistancePositive :
    0 < distanceInLightYears setup.sourceEarthDistance
  everyLaboratoryWavelengthPositive : ∀ line,
    0 < wavelengthInNanometers (setup.laboratoryWavelength line)
  everyObservedWavelengthPositive : ∀ line,
    0 < wavelengthInNanometers (setup.earthObservedWavelength line)
  lightSpeedPositive : 0 < vacuumSpeedOfLightInMetersPerSecond
  radialSpeedNonnegative :
    0 ≤ speedInMetersPerSecond setup.radialSpeedRelativeToEarth

/-! ## Governing Doppler law -/

/-!
The standard low-speed radial optical Doppler model, applied uniformly to all
emission lines from one source.  The response function gives the exact
fractional wavelength shift predicted by the chosen radial model.  Its
derivative at rest is one, and the explicit quadratic remainder estimate is
restricted to the receding low-speed neighborhood `0 ≤ v / c ≤ 1 / 10`.

Thus the familiar relation `Δλ / λ₀ ≈ v / c` is represented as a controlled
local approximation, not as a globally exact equality.  This structure does
not state the calculated speed or select an answer choice.
-/
structure SatisfiesLowSpeedRadialOpticalDopplerLaw
    {SpectralLine : Type} (setup : GalaxyRedshiftSetup SpectralLine) : Type where
  fractionalShiftResponse : ℝ → ℝ
  zeroShiftAtRest : fractionalShiftResponse 0 = 0
  firstOrderResponseAtRest : HasDerivAt fractionalShiftResponse 1 0
  actualSpeedFractionInLowSpeedNeighborhood :
    speedInMetersPerSecond setup.radialSpeedRelativeToEarth /
        vacuumSpeedOfLightInMetersPerSecond ∈ Set.Icc 0 (1 / 10 : ℝ)
  observedShiftFromResponse : ∀ line,
    fractionalShiftResponse
          (speedInMetersPerSecond setup.radialSpeedRelativeToEarth /
            vacuumSpeedOfLightInMetersPerSecond) =
      (wavelengthInNanometers (setup.earthObservedWavelength line) -
          wavelengthInNanometers (setup.laboratoryWavelength line)) /
        wavelengthInNanometers (setup.laboratoryWavelength line)
  quadraticRemainderInLowSpeedNeighborhood : ∀ β ∈ Set.Icc 0 (1 / 10 : ℝ),
    |fractionalShiftResponse β - β| ≤ β ^ 2

/-! ## Displayed choices and current target -/

/-- Labels of the four radial-speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed candidate radial speeds, in metres per second. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 300000
  | .B => 70000000
  | .C => 7000000
  | .D => 2000000

/-- Absolute error between the physical radial speed and a displayed choice. -/
def answerChoiceErrorMetersPerSecond
    {SpectralLine : Type} (setup : GalaxyRedshiftSetup SpectralLine)
    (choice : AnswerChoice) : ℝ :=
  |speedInMetersPerSecond setup.radialSpeedRelativeToEarth -
    choice.metersPerSecond|

/-- A displayed speed is strictly closer than every competing choice. -/
def IsUniqueClosestRadialSpeedChoice
    {SpectralLine : Type} (setup : GalaxyRedshiftSetup SpectralLine)
    (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorMetersPerSecond setup choice <
      answerChoiceErrorMetersPerSecond setup other

/-!
The oxygen line gives `Δλ / λ₀ = 12 / 513`.  The local Doppler remainder
contract bounds the difference between the actual radial speed and the
first-order estimate `c * (12 / 513)`.  That controlled interval uniquely
selects the displayed choice `7.0 × 10^6 m/s` (choice C); it does not assert
that the first-order estimate is the exact physical speed.

Blueprint label: `thm:physics:phyx_mini_0596:target`.
-/
theorem radialSpeedOfNGC7319_is_choiceC
    {SpectralLine : Type} (setup : GalaxyRedshiftSetup SpectralLine)
    (_scenario : MatchesNGC7319SpectrumScenario setup)
    (_figure : MatchesPrimarySpectrumFigure setup)
    (_readouts : MatchesNGC7319ProblemReadouts setup)
    (_physical : HasPhysicalRedshiftParameters setup)
    (_doppler : SatisfiesLowSpeedRadialOpticalDopplerLaw setup) :
    |speedInMetersPerSecond setup.radialSpeedRelativeToEarth -
          vacuumSpeedOfLightInMetersPerSecond * (12 / 513 : ℝ)| ≤
        vacuumSpeedOfLightInMetersPerSecond *
          (speedInMetersPerSecond setup.radialSpeedRelativeToEarth /
            vacuumSpeedOfLightInMetersPerSecond) ^ 2 ∧
      IsUniqueClosestRadialSpeedChoice setup .C := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0596
