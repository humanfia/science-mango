import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Gauge pressure in a narrowing, rising water pipe

The primary raster shows water flowing from section `1` in a lower horizontal
pipe to section `2` in a narrower upper horizontal pipe.  The marked diameters
are `6.0 cm` and `4.0 cm`, section `2` is `2.0 m` above section `1`, and the
lower-section readouts are `5.0 m/s` and `75 kPa` gauge pressure.  The requested
quantity is the gauge-pressure reading at section `2`.

Pressure, speed, area, length, mass density, and acceleration are represented
by unit-independent Physlib quantities.  Real numbers occur only as named-unit
readouts, in dimensionally homogeneous scalar forms of the governing laws, and
in the displayed answer table.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0724

open Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of a choice of units. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass density. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the two pipe-diameter labels. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI square-metre readout of a physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Coherent-SI pascal readout of a pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used by both pressure gauges and all answer choices. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Coherent-SI kilogram-per-cubic-metre readout of a mass density. -/
def densityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-! ## Pipe, fluid, and primary-figure vocabulary -/

/-- The numbered cross sections marked by black dots in the primary image. -/
inductive PipeSection where
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- Fluids relevant to the physical role of the pipe contents. -/
inductive FluidKind where
  | water
  | other
  deriving DecidableEq, Repr

/-- The reference convention used by a pressure-gauge readout. -/
inductive PressureReference where
  | gaugeRelativeToAtmosphere
  | absolute
  deriving DecidableEq, Repr

/-- Horizontal ordering of the two marked sections in the supplied raster. -/
inductive HorizontalFigureLocation where
  | left
  | right
  deriving DecidableEq, Repr

/-- Vertical ordering of the two marked sections in the supplied raster. -/
inductive VerticalFigureLocation where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- Direction of a green flow arrow in the supplied raster. -/
inductive HorizontalFlowDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-!
Literal labels and qualitative features visible in image `724.png`.  The
unknown upper gauge is represented by its question-mark label, not by a
numerical pressure value.
-/
structure WaterPipeFigure where
  sectionNumberText : PipeSection → String
  diameterText : PipeSection → String
  speedText : PipeSection → String
  pressureGaugeText : PipeSection → String
  horizontalLocation : PipeSection → HorizontalFigureLocation
  verticalLocation : PipeSection → VerticalFigureLocation
  flowArrowDirection : PipeSection → HorizontalFlowDirection
  heightDifferenceText : String
  showsSectionCenterMarker : PipeSection → Bool
  showsPressureGaugeTap : PipeSection → Bool
  showsDiameterArrow : PipeSection → Bool
  showsWaterFilledPipe : Bool
  showsNarrowingUpwardConnector : Bool
  showsVerticalHeightArrow : Bool

/-!
The physical state at one marked cross section.  In particular, the pressure
and speed at section `2` are independent observables; neither is defined from
the recorded answer.
-/
structure PipeSectionState where
  diameter : LengthQuantity
  crossSectionalArea : DimArea
  elevation : LengthQuantity
  speed : DimSpeed
  gaugePressure : DimPressure

/-!
The independent physical quantities and ideal-flow descriptors for the
experiment.  `verticalRise` is the centreline rise from section `1` to section
`2`, as indicated by the vertical `2.0 m` dimension arrow.
-/
structure RisingPipeSetup where
  fluid : FluidKind
  pressureReference : PressureReference
  stateAt : PipeSection → PipeSectionState
  verticalRise : LengthQuantity
  waterMassDensity : MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  flowIsSteady : Bool
  fluidIsIncompressible : Bool
  viscousLossIsNegligible : Bool
  sectionsLieOnSameStreamline : Bool
  figure : WaterPipeFigure

/-! ## Scenario, figure evidence, and data readouts -/

/-!
The textbook Bernoulli model used for the stated water-flow scenario.  Gauge
pressures share the same atmospheric reference, so their difference may be
used in Bernoulli's equation.
-/
structure MatchesIdealWaterPipeScenario (setup : RisingPipeSetup) : Prop where
  flowingFluidIsWater : setup.fluid = .water
  pressuresAreGaugeReadings :
    setup.pressureReference = .gaugeRelativeToAtmosphere
  flowIsSteady : setup.flowIsSteady = true
  waterIsIncompressible : setup.fluidIsIncompressible = true
  negligibleViscousLoss : setup.viscousLossIsNegligible = true
  sameStreamline : setup.sectionsLieOnSameStreamline = true

/-!
Transcription of the literal labels, section ordering, green arrows, gauge
taps, diameter markers, and rising connector in the primary raster.  This
contains no numerical value for the upper gauge pressure.
-/
structure MatchesPrimaryPipeFigure (setup : RisingPipeSetup) : Prop where
  sectionOneNumber : setup.figure.sectionNumberText .one = "1"
  sectionTwoNumber : setup.figure.sectionNumberText .two = "2"
  lowerDiameterLabel : setup.figure.diameterText .one = "6.0 cm"
  upperDiameterLabel : setup.figure.diameterText .two = "4.0 cm"
  lowerSpeedLabel : setup.figure.speedText .one = "5.0 m/s"
  upperSpeedLabel : setup.figure.speedText .two = "v₂"
  lowerGaugeLabel : setup.figure.pressureGaugeText .one = "75 kPa"
  upperGaugeUnknownLabel : setup.figure.pressureGaugeText .two = "?"
  riseLabel : setup.figure.heightDifferenceText = "2.0 m"
  sectionOneIsLeft : setup.figure.horizontalLocation .one = .left
  sectionTwoIsRight : setup.figure.horizontalLocation .two = .right
  sectionOneIsLower : setup.figure.verticalLocation .one = .lower
  sectionTwoIsUpper : setup.figure.verticalLocation .two = .upper
  lowerArrowPointsRight :
    setup.figure.flowArrowDirection .one = .leftToRight
  upperArrowPointsRight :
    setup.figure.flowArrowDirection .two = .leftToRight
  centerMarkersShown : ∀ pipeSection,
    setup.figure.showsSectionCenterMarker pipeSection = true
  gaugeTapsShown : ∀ pipeSection,
    setup.figure.showsPressureGaugeTap pipeSection = true
  diameterArrowsShown : ∀ pipeSection,
    setup.figure.showsDiameterArrow pipeSection = true
  waterFilledPipeShown : setup.figure.showsWaterFilledPipe = true
  narrowingRiseShown : setup.figure.showsNarrowingUpwardConnector = true
  verticalHeightArrowShown : setup.figure.showsVerticalHeightArrow = true

/-!
The five numerical values supplied by the prose and the primary raster.  The
upper speed and upper pressure deliberately do not occur as numerical data.
-/
structure MatchesProblemReadouts (setup : RisingPipeSetup) : Prop where
  lowerDiameterCentimeters :
    lengthInCentimeters (setup.stateAt .one).diameter = 6
  upperDiameterCentimeters :
    lengthInCentimeters (setup.stateAt .two).diameter = 4
  lowerSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.stateAt .one).speed = 5
  lowerGaugePressureKilopascals :
    pressureInKilopascals (setup.stateAt .one).gaugePressure = 75
  sectionRiseMeters : lengthInMeters setup.verticalRise = 2

/-!
Standard textbook calibration implicit in the numerical answer: water has
density `1000 kg/m³`, and gravitational acceleration is taken as `9.8 m/s²`.
-/
structure UsesTextbookWaterDensityAndGravity
    (setup : RisingPipeSetup) : Prop where
  waterDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter setup.waterMassDensity = 1000
  gravitationalAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-! ## Pipe geometry and governing flow laws -/

/-!
Both labelled diameters describe circular cross sections, and the marked
`2.0 m` arrow is the centreline elevation difference.  These are geometric
relations, not solved pressure or velocity formulas.
-/
structure SatisfiesCircularRisingPipeGeometry
    (setup : RisingPipeSetup) : Prop where
  lowerCircularCrossSection :
    areaInSquareMeters (setup.stateAt .one).crossSectionalArea =
      Real.pi * (lengthInMeters (setup.stateAt .one).diameter / 2) ^ 2
  upperCircularCrossSection :
    areaInSquareMeters (setup.stateAt .two).crossSectionalArea =
      Real.pi * (lengthInMeters (setup.stateAt .two).diameter / 2) ^ 2
  upperElevationFromMarkedRise :
    lengthInMeters (setup.stateAt .two).elevation =
      lengthInMeters (setup.stateAt .one).elevation +
        lengthInMeters setup.verticalRise

/-!
The steady incompressible continuity equation and Bernoulli equation between
the two marked section centres, written in coherent SI readouts.  The latter
uses a common gauge-pressure reference and contains no problem-specific solved
upper pressure.
-/
structure SatisfiesIdealPipeFlowLaws (setup : RisingPipeSetup) : Prop where
  steadyIncompressibleContinuity :
    areaInSquareMeters (setup.stateAt .one).crossSectionalArea *
        speedInMetersPerSecond (setup.stateAt .one).speed =
      areaInSquareMeters (setup.stateAt .two).crossSectionalArea *
        speedInMetersPerSecond (setup.stateAt .two).speed
  bernoulliBetweenGaugeTaps :
    pressureInPascals (setup.stateAt .one).gaugePressure +
          (1 / 2 : ℝ) *
            densityInKilogramsPerCubicMeter setup.waterMassDensity *
            speedInMetersPerSecond (setup.stateAt .one).speed ^ 2 +
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters (setup.stateAt .one).elevation =
      pressureInPascals (setup.stateAt .two).gaugePressure +
          (1 / 2 : ℝ) *
            densityInKilogramsPerCubicMeter setup.waterMassDensity *
            speedInMetersPerSecond (setup.stateAt .two).speed ^ 2 +
        densityInKilogramsPerCubicMeter setup.waterMassDensity *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters (setup.stateAt .two).elevation

/-! ## Derived section values and displayed answer -/

/-!
Circular-section geometry and continuity give
`v₂ = 5 (6/4)² = 45/4 m/s`.
-/
lemma upper_speed_from_continuity
    (setup : RisingPipeSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : SatisfiesCircularRisingPipeGeometry setup)
    (hLaws : SatisfiesIdealPipeFlowLaws setup) :
    speedInMetersPerSecond (setup.stateAt .two).speed = 45 / 4 := by
  have hLowerDiameter := hReadouts.lowerDiameterCentimeters
  have hUpperDiameter := hReadouts.upperDiameterCentimeters
  dsimp [lengthInCentimeters] at hLowerDiameter hUpperDiameter
  have hLowerDiameterMeters :
      lengthInMeters (setup.stateAt .one).diameter = 3 / 50 := by
    linarith
  have hUpperDiameterMeters :
      lengthInMeters (setup.stateAt .two).diameter = 1 / 25 := by
    linarith
  have hLowerArea := hGeometry.lowerCircularCrossSection
  have hUpperArea := hGeometry.upperCircularCrossSection
  rw [hLowerDiameterMeters] at hLowerArea
  rw [hUpperDiameterMeters] at hUpperArea
  norm_num at hLowerArea hUpperArea
  have hContinuity := hLaws.steadyIncompressibleContinuity
  rw [hLowerArea, hUpperArea, hReadouts.lowerSpeedMetersPerSecond] at hContinuity
  nlinarith [Real.pi_pos]

/-!
Substitution into Bernoulli's equation gives the exact idealized upper gauge
pressure `18475/4 Pa = 739/160 kPa`.
-/
lemma upper_gauge_pressure_in_pascals
    (setup : RisingPipeSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hCalibration : UsesTextbookWaterDensityAndGravity setup)
    (hGeometry : SatisfiesCircularRisingPipeGeometry setup)
    (hLaws : SatisfiesIdealPipeFlowLaws setup) :
    pressureInPascals (setup.stateAt .two).gaugePressure = 18475 / 4 := by
  have hLowerPressure := hReadouts.lowerGaugePressureKilopascals
  dsimp [pressureInKilopascals] at hLowerPressure
  have hLowerPressurePascals :
      pressureInPascals (setup.stateAt .one).gaugePressure = 75000 := by
    linarith
  have hUpperSpeed :=
    upper_speed_from_continuity setup hReadouts hGeometry hLaws
  have hBernoulli := hLaws.bernoulliBetweenGaugeTaps
  rw [hLowerPressurePascals, hReadouts.lowerSpeedMetersPerSecond,
    hUpperSpeed, hCalibration.waterDensityKilogramsPerCubicMeter,
    hCalibration.gravitationalAccelerationMetersPerSecondSquared,
    hGeometry.upperElevationFromMarkedRise, hReadouts.sectionRiseMeters]
    at hBernoulli
  norm_num at hBernoulli ⊢
  linarith

/-- Labels of the four pressure readings printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kilopascal value printed beside each displayed answer choice. -/
def displayedGaugePressureKilopascals : AnswerChoice → ℝ
  | .A => 22 / 5
  | .B => 24 / 5
  | .C => 23 / 5
  | .D => 5

/-!
A reading displayed to the nearest `0.1 kPa` differs from the exact idealized
readout by strictly less than `0.05 kPa`.
-/
def RoundsToNearestTenthKilopascal
    (exactReading displayedReading : ℝ) : Prop :=
  |exactReading - displayedReading| < 1 / 20

/-- A displayed choice agrees with the modeled upper gauge to its precision. -/
def MatchesDisplayedUpperGaugePressure
    (setup : RisingPipeSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenthKilopascal
    (pressureInKilopascals (setup.stateAt .two).gaugePressure)
    (displayedGaugePressureKilopascals choice)

/-- Exactly one printed choice agrees with the modeled upper gauge reading. -/
def IsUniqueMatchingUpperGaugePressure
    (setup : RisingPipeSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedUpperGaugePressure setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedUpperGaugePressure setup other → other = choice

/-!
The ideal-flow calculation gives `4.61875 kPa`, which rounds to `4.6 kPa` and
uniquely selects choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0724:target`.
-/
theorem problem_phyx_mini_0724
    (setup : RisingPipeSetup)
    (_scenario : MatchesIdealWaterPipeScenario setup)
    (_figure : MatchesPrimaryPipeFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hCalibration : UsesTextbookWaterDensityAndGravity setup)
    (hGeometry : SatisfiesCircularRisingPipeGeometry setup)
    (hLaws : SatisfiesIdealPipeFlowLaws setup) :
    pressureInPascals (setup.stateAt .two).gaugePressure = 18475 / 4 ∧
      pressureInKilopascals (setup.stateAt .two).gaugePressure = 739 / 160 ∧
      IsUniqueMatchingUpperGaugePressure setup .C := by
  have hPressure :=
    upper_gauge_pressure_in_pascals
      setup hReadouts hCalibration hGeometry hLaws
  have hPressureKilopascals :
      pressureInKilopascals (setup.stateAt .two).gaugePressure = 739 / 160 := by
    rw [pressureInKilopascals, hPressure]
    norm_num
  refine ⟨hPressure, hPressureKilopascals, ?_⟩
  constructor
  · norm_num [MatchesDisplayedUpperGaugePressure,
      RoundsToNearestTenthKilopascal, displayedGaugePressureKilopascals,
      hPressureKilopascals]
  · intro other hOther
    cases other with
    | A =>
        norm_num [MatchesDisplayedUpperGaugePressure,
          RoundsToNearestTenthKilopascal, displayedGaugePressureKilopascals,
          hPressureKilopascals] at hOther
    | B =>
        norm_num [MatchesDisplayedUpperGaugePressure,
          RoundsToNearestTenthKilopascal, displayedGaugePressureKilopascals,
          hPressureKilopascals] at hOther
    | C => rfl
    | D =>
        norm_num [MatchesDisplayedUpperGaugePressure,
          RoundsToNearestTenthKilopascal, displayedGaugePressureKilopascals,
          hPressureKilopascals] at hOther

end PhyXMiniProblems.ProblemPhyXMini0724
