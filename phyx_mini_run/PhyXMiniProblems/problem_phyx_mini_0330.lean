import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

/-!
# Two-path sound interference at a reflecting wall

This file models problem `phyx_mini_0330`. A point source `S` and detector
`D` are on the same side of the vertical wall `AB`. Ray `R1` travels directly
from `S` to `D`, while ray `R2` reflects once from the wall with equal angles
of incidence and reflection. The reflection contributes a phase displacement
of one half-wavelength.

Lengths, frequencies, and speeds are represented by unit-independent Physlib
quantities. Real numbers occur only as named unit readouts, angles and phase
fractions (which are dimensionless), integer orders coerced to scalars, and
displayed whole-hertz answer data.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0330

open Dimension

/-! ## Dimensionful acoustic quantities and unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative cyclic frequency, carrying the inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed. -/
abbrev AcousticSpeed : Type := DimSpeed

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical cyclic frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed in the selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : AcousticSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
      length := lengthUnit
      time := timeUnit}).val : ℝ)

/-- Metre readout used for the three distances and the ray path lengths. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Metre-per-second readout of the sound speed. -/
def speedInMetersPerSecond (speed : AcousticSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Primary-figure labels and physical setup -/

/-- The four literal point labels printed in the primary figure. -/
inductive FigurePoint where
  | A
  | B
  | S
  | D
  deriving DecidableEq, Repr

/-- The label of the reflecting wall segment. -/
inductive WallLabel where
  | AB
  deriving DecidableEq, Repr

/-- The orientation of wall `AB` in the supplied figure. -/
inductive WallOrientation where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- The two red sound-ray labels printed in the figure. -/
inductive SoundRay where
  | R1
  | R2
  deriving DecidableEq, Repr

/-- The geometric behavior of a depicted sound ray. -/
inductive RayRouteKind where
  | direct
  | singleReflectionAtWall
  deriving DecidableEq, Repr

/-- The relative placement of `D` visible in the figure. -/
inductive DetectorPlacement where
  | rightAndBelowSource
  | other
  deriving DecidableEq, Repr

/-- The propagation medium implicit in the sound-reflection experiment. -/
inductive AcousticMedium where
  | air
  | other
  deriving DecidableEq, Repr

/-- A red ray drawn from the labelled source to the labelled detector. -/
structure DepictedSoundRay where
  sourcePoint : FigurePoint
  detectorPoint : FigurePoint
  routeKind : RayRouteKind

/-!
Qualitative information and dimensionless angles read from the primary image.
The incidence and reflection angles belong to the unique wall encounter of
`R2`; their equality is imposed later as the law of specular reflection.
-/
structure SoundReflectionFigure where
  pointLabelShown : FigurePoint → Bool
  wallLabel : WallLabel
  wallOrientation : WallOrientation
  wallUpperEndpoint : FigurePoint
  wallLowerEndpoint : FigurePoint
  ray : SoundRay → DepictedSoundRay
  detectorPlacement : DetectorPlacement
  d1AndD2ShownHorizontal : Bool
  d3ShownVertical : Bool
  rightAngleAtDetectorProjectionShown : Bool
  incidenceAngleLabelShown : Bool
  reflectionAngleLabelShown : Bool
  incidenceAngleRadians : ℝ
  reflectionAngleRadians : ℝ

/-!
The independent physical quantities of the experiment.

`d1` is the perpendicular horizontal distance from wall `AB` to source `S`;
`d2` is the horizontal separation from `S` to the vertical line through `D`;
and `d3` is the vertical separation down to `D`. `rayPathLength`,
`pathDifference`, `wavelengthAtFrequency`, and `inPhaseAtDetector` are
independent physical observables constrained only by the governing laws below.
-/
structure WallReflectedSoundSetup where
  figure : SoundReflectionFigure
  medium : AcousticMedium
  d1WallToSource : AcousticLength
  d2SourceToDetectorProjection : AcousticLength
  d3VerticalToDetector : AcousticLength
  rayPathLength : SoundRay → AcousticLength
  pathDifference : AcousticLength
  soundSpeed : AcousticSpeed
  wavelengthAtFrequency : AcousticFrequency → AcousticLength
  reflectionPhaseShiftWavelengths : ℝ
  inPhaseAtDetector : AcousticFrequency → Prop

/-!
Labels, routes, and relative placement transcribed from the primary bitmap.
Both rays start at `S` and reach `D`; `R1` is direct and `R2` reflects once
from wall `AB`. No path length, frequency, or interference conclusion is
contained here.
-/
structure MatchesSuppliedFigure (setup : WallReflectedSoundSetup) : Prop where
  allPointLabelsShown : ∀ point, setup.figure.pointLabelShown point = true
  wallIsAB : setup.figure.wallLabel = .AB
  wallIsVertical : setup.figure.wallOrientation = .vertical
  AIsUpperWallEndpoint : setup.figure.wallUpperEndpoint = .A
  BIsLowerWallEndpoint : setup.figure.wallLowerEndpoint = .B
  R1IsDirect :
    setup.figure.ray .R1 =
      { sourcePoint := .S
        detectorPoint := .D
        routeKind := .direct }
  R2ReflectsAtWall :
    setup.figure.ray .R2 =
      { sourcePoint := .S
        detectorPoint := .D
        routeKind := .singleReflectionAtWall }
  detectorIsRightAndBelowSource :
    setup.figure.detectorPlacement = .rightAndBelowSource
  d1AndD2AreShownHorizontal : setup.figure.d1AndD2ShownHorizontal = true
  d3IsShownVertical : setup.figure.d3ShownVertical = true
  detectorProjectionRightAngleIsShown :
    setup.figure.rightAngleAtDetectorProjectionShown = true
  incidenceAngleLabelIsShown : setup.figure.incidenceAngleLabelShown = true
  reflectionAngleLabelIsShown : setup.figure.reflectionAngleLabelShown = true

/-!
Numerical data printed in the problem. The terminating decimals are represented
exactly as rational real readouts. The stated `0.500 lambda` reflection shift
is the dimensionless fraction `1/2`; it is not a wavelength or frequency
answer.
-/
structure MatchesProblemReadouts (setup : WallReflectedSoundSetup) : Prop where
  mediumIsAir : setup.medium = .air
  d1Meters : lengthInMeters setup.d1WallToSource = 5 / 2
  d2Meters : lengthInMeters setup.d2SourceToDetectorProjection = 20
  d3Meters : lengthInMeters setup.d3VerticalToDetector = 25 / 2
  reflectionPhaseShiftIsHalfWavelength :
    setup.reflectionPhaseShiftWavelengths = 1 / 2

/-!
The problem does not print a propagation speed. This separate calibration
records the conventional room-temperature value `343 m/s` used to evaluate
the whole-hertz answer choices.
-/
def UsesStandardAirSoundSpeed (setup : WallReflectedSoundSetup) : Prop :=
  speedInMetersPerSecond setup.soundSpeed = 343

/-- Positivity and nondegeneracy conditions for the physical setup. -/
structure HasPhysicalAcousticParameters
    (setup : WallReflectedSoundSetup) : Prop where
  d1Positive : ∀ unit, 0 < lengthReadout unit setup.d1WallToSource
  d2Positive : ∀ unit,
    0 < lengthReadout unit setup.d2SourceToDetectorProjection
  d3Positive : ∀ unit, 0 < lengthReadout unit setup.d3VerticalToDetector
  soundSpeedPositive : ∀ lengthUnit timeUnit,
    0 < speedReadout lengthUnit timeUnit setup.soundSpeed
  positiveFrequencyHasPositiveWavelength :
    ∀ frequency,
      0 < frequencyInHertz frequency →
        ∀ unit, 0 < lengthReadout unit (setup.wavelengthAtFrequency frequency)

/-! ## Governing geometry and acoustic laws -/

/-- The reflected ray obeys the equal-angle law at wall `AB`. -/
structure SatisfiesSpecularReflection
    (setup : WallReflectedSoundSetup) : Prop where
  incidenceAngleNonnegative : 0 ≤ setup.figure.incidenceAngleRadians
  reflectionAngleNonnegative : 0 ≤ setup.figure.reflectionAngleRadians
  incidenceEqualsReflection :
    setup.figure.incidenceAngleRadians = setup.figure.reflectionAngleRadians

/-!
The direct length follows from the `d2` by `d3` right triangle. For the
reflected length, mirroring `S` across the vertical wall changes the horizontal
leg to `2*d1 + d2`; the unfolded ray is then another right-triangle
hypotenuse. These are general figure-geometry equations in any length unit.
-/
structure SatisfiesWallReflectionPathGeometry
    (setup : WallReflectedSoundSetup) : Prop where
  directPathLength : ∀ unit,
    lengthReadout unit (setup.rayPathLength .R1) =
      Real.sqrt
        ((lengthReadout unit setup.d2SourceToDetectorProjection) ^ 2 +
          (lengthReadout unit setup.d3VerticalToDetector) ^ 2)
  reflectedPathLength : ∀ unit,
    lengthReadout unit (setup.rayPathLength .R2) =
      Real.sqrt
        ((2 * lengthReadout unit setup.d1WallToSource +
            lengthReadout unit setup.d2SourceToDetectorProjection) ^ 2 +
          (lengthReadout unit setup.d3VerticalToDetector) ^ 2)

/-- The path difference is the magnitude of the two ray-length difference. -/
structure SatisfiesPathDifferenceLaw
    (setup : WallReflectedSoundSetup) : Prop where
  pathDifferenceFromRayLengths : ∀ unit,
    lengthReadout unit setup.pathDifference =
      |lengthReadout unit (setup.rayPathLength .R2) -
        lengthReadout unit (setup.rayPathLength .R1)|

/-!
The nondispersive sound-wave relation `v = lambda*f`, stated in compatible
arbitrary length and time units. It characterizes wavelength at every positive
frequency without assigning the requested frequency.
-/
structure SatisfiesSoundSpeedFrequencyWavelengthLaw
    (setup : WallReflectedSoundSetup) : Prop where
  speedEqualsWavelengthTimesFrequency :
    ∀ frequency,
      0 < frequencyInHertz frequency →
        ∀ lengthUnit timeUnit,
          speedReadout lengthUnit timeUnit setup.soundSpeed =
            lengthReadout lengthUnit
                (setup.wavelengthAtFrequency frequency) *
              frequencyReadout timeUnit frequency

/-!
For coherent rays from one point source, arrival is in phase exactly when the
propagation path difference plus the reflection phase displacement is an
integral number of wavelengths. The positive natural `order` ranges over the
entire constructive-interference spectrum, so this law does not select the
first, second, or any numerical frequency.
-/
structure SatisfiesReflectedSoundInterferenceLaw
    (setup : WallReflectedSoundSetup) : Prop where
  inPhaseIffIntegralTotalPhase :
    ∀ frequency,
      0 < frequencyInHertz frequency →
        (setup.inPhaseAtDetector frequency ↔
          ∃ order : ℕ,
            0 < order ∧
              ∀ unit,
                lengthReadout unit setup.pathDifference +
                    setup.reflectionPhaseShiftWavelengths *
                      lengthReadout unit
                        (setup.wavelengthAtFrequency frequency) =
                  (order : ℝ) *
                    lengthReadout unit
                      (setup.wavelengthAtFrequency frequency))

/-! ## Frequency ordering and displayed answers -/

/-- A positive physical frequency at which the two received rays are in phase. -/
def IsPositiveInPhaseFrequency
    (setup : WallReflectedSoundSetup)
    (frequency : AcousticFrequency) : Prop :=
  0 < frequencyInHertz frequency ∧ setup.inPhaseAtDetector frequency

/-- A least positive in-phase frequency, expressed through its hertz order. -/
def IsLowestPositiveInPhaseFrequency
    (setup : WallReflectedSoundSetup)
    (frequency : AcousticFrequency) : Prop :=
  IsPositiveInPhaseFrequency setup frequency ∧
    ∀ other : AcousticFrequency,
      IsPositiveInPhaseFrequency setup other →
        frequencyInHertz frequency ≤ frequencyInHertz other

/-!
`frequency` is second-lowest when a lowest positive in-phase frequency lies
strictly below it and it is no greater than any positive in-phase frequency
strictly above that lowest one. This generic definition contains no numerical
frequency, interference order, or answer label.
-/
def IsSecondLowestInPhaseFrequency
    (setup : WallReflectedSoundSetup)
    (frequency : AcousticFrequency) : Prop :=
  IsPositiveInPhaseFrequency setup frequency ∧
    ∃ lowest : AcousticFrequency,
      IsLowestPositiveInPhaseFrequency setup lowest ∧
        frequencyInHertz lowest < frequencyInHertz frequency ∧
        ∀ other : AcousticFrequency,
          IsPositiveInPhaseFrequency setup other →
            frequencyInHertz lowest < frequencyInHertz other →
              frequencyInHertz frequency ≤ frequencyInHertz other

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Whole-hertz value displayed beside each answer label. -/
def AnswerChoice.hertz : AnswerChoice → ℝ
  | .A => 98
  | .B => 102
  | .C => 109
  | .D => 118

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A physical frequency rounds to a displayed whole-hertz value. -/
def RoundsToWholeHertz
    (frequency : AcousticFrequency) (wholeHertz : ℝ) : Prop :=
  |frequencyInHertz frequency - wholeHertz| < 1 / 2

/-- A physical frequency agrees, after rounding, with a displayed choice. -/
def AgreesWithDisplayedFrequencyChoice
    (frequency : AcousticFrequency) (choice : AnswerChoice) : Prop :=
  RoundsToWholeHertz frequency choice.hertz

/-!
The image-source geometry and the supplied distance readouts give the exact
SI path difference

`sqrt (25^2 + (25/2)^2) - sqrt (20^2 + (25/2)^2)` metres.

This helper is a geometric consequence, not a frequency conclusion.
-/
lemma pathDifferenceInMeters_exact
    (setup : WallReflectedSoundSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hGeometry : SatisfiesWallReflectionPathGeometry setup)
    (hDifference : SatisfiesPathDifferenceLaw setup) :
    lengthInMeters setup.pathDifference =
      Real.sqrt (25 ^ 2 + (25 / 2 : ℝ) ^ 2) -
        Real.sqrt (20 ^ 2 + (25 / 2 : ℝ) ^ 2) := by
  sorry

/-!
With a half-wavelength reflection phase shift, consecutive in-phase orders
have `Delta L = (order - 1/2) lambda`. Thus the second positive order has
`f = 3 v / (2 Delta L)`. The existential frequency is still a dimensionful
physical quantity; this lemma does not round it or mention an answer choice.
-/
lemma secondLowestInPhaseFrequency_formula
    (setup : WallReflectedSoundSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hGeometry : SatisfiesWallReflectionPathGeometry setup)
    (hDifference : SatisfiesPathDifferenceLaw setup)
    (hWaveLaw : SatisfiesSoundSpeedFrequencyWavelengthLaw setup)
    (hInterference : SatisfiesReflectedSoundInterferenceLaw setup) :
    ∃ frequency : AcousticFrequency,
      IsSecondLowestInPhaseFrequency setup frequency ∧
        frequencyInHertz frequency =
          3 * speedInMetersPerSecond setup.soundSpeed /
            (2 * lengthInMeters setup.pathDifference) := by
  sorry

/-!
The source-faithful result leaves the sound speed symbolic, because the
problem statement supplies the three distances and reflection phase shift but
does not print a numerical propagation speed. The second-lowest frequency is

`3*v / (2*(sqrt (25^2 + 12.5^2) - sqrt (20^2 + 12.5^2))) Hz`.

Blueprint: `thm:physics:phyx_mini_0330:target`.
-/
theorem problem_phyx_mini_0330
    (setup : WallReflectedSoundSetup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hReflection : SatisfiesSpecularReflection setup)
    (hGeometry : SatisfiesWallReflectionPathGeometry setup)
    (hDifference : SatisfiesPathDifferenceLaw setup)
    (hWaveLaw : SatisfiesSoundSpeedFrequencyWavelengthLaw setup)
    (hInterference : SatisfiesReflectedSoundInterferenceLaw setup) :
    ∃ frequency : AcousticFrequency,
      IsSecondLowestInPhaseFrequency setup frequency ∧
        frequencyInHertz frequency =
          3 * speedInMetersPerSecond setup.soundSpeed /
            (2 *
              (Real.sqrt (25 ^ 2 + (25 / 2 : ℝ) ^ 2) -
                Real.sqrt (20 ^ 2 + (25 / 2 : ℝ) ^ 2))) := by
  sorry

/-!
If one separately adopts the conventional room-air calibration `343 m/s`,
the symbolic result is approximately `117.845 Hz`. It therefore rounds to
`118 Hz` and agrees with displayed and recorded choice D. This is deliberately
a conditional corollary rather than part of the source-faithful target.
-/
theorem problem_phyx_mini_0330_atStandardAirSpeed
    (setup : WallReflectedSoundSetup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hAirSpeed : UsesStandardAirSoundSpeed setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hReflection : SatisfiesSpecularReflection setup)
    (hGeometry : SatisfiesWallReflectionPathGeometry setup)
    (hDifference : SatisfiesPathDifferenceLaw setup)
    (hWaveLaw : SatisfiesSoundSpeedFrequencyWavelengthLaw setup)
    (hInterference : SatisfiesReflectedSoundInterferenceLaw setup) :
    ∃ frequency : AcousticFrequency,
      IsSecondLowestInPhaseFrequency setup frequency ∧
        frequencyInHertz frequency =
          3 * 343 /
            (2 *
              (Real.sqrt (25 ^ 2 + (25 / 2 : ℝ) ^ 2) -
                Real.sqrt (20 ^ 2 + (25 / 2 : ℝ) ^ 2))) ∧
        RoundsToWholeHertz frequency 118 ∧
        AgreesWithDisplayedFrequencyChoice frequency recordedDatasetAnswer := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0330
