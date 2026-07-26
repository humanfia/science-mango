import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0301

/-!
# Speed of a translated pulse

The source specifies a one-dimensional scalar pulse of the form
`h(x - 5.0 t)`. Position readouts are in centimeters and time readouts are
in seconds. The raster at `t = 0` shows a triangular pulse: it is zero up to
`x = 1`, rises to the height `h_s = 2` at `x = 3`, and returns to zero at
`x = 4`. The raster, which is the primary evidence, places the right foot at
`4`, although the auxiliary caption says `5`.

The propagation speed itself is represented by Physlib's unit-independent
`DimSpeed`. Real numbers occur only as coordinates, times, scalar pulse
heights, and numerical readouts in explicitly selected units.
-/

/-! ## Dimensionful speed and unit readouts -/

/-- A nonnegative physical speed, independent of the unit used to read it. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- The speed readout in the units used by the problem, centimeters per second. -/
def speedInCentimetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.centimeters TimeUnit.seconds speed

/-! ## Primary-figure labels and geometry -/

/-- Textual and symbolic labels visibly printed in the pulse raster. -/
inductive PulseFigureLabel where
  | horizontalCoordinateX
  | profileHOfX
  | heightScaleHs
  | timeEqualsZero
  deriving DecidableEq, Repr

/-- Direction along the one-dimensional horizontal coordinate axis. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Sign used to turn a nonnegative speed readout into an axial velocity. -/
def directionSign : HorizontalDirection → ℝ
  | .left => -1
  | .right => 1

/-!
All numerical geometry read directly from the primary raster. Coordinates
have an `Cm` suffix because the horizontal axis is in centimeters. No physical
unit is stated for the vertical pulse height, so it remains a scalar readout.
-/
structure PulseFigure where
  horizontalAxisUnit : LengthUnit
  timeUnit : TimeUnit
  horizontalAxisMinimumCm : ℝ
  horizontalAxisMaximumCm : ℝ
  verticalAxisMinimumReadout : ℝ
  leftFootCm : ℝ
  peakPositionCm : ℝ
  rightFootCm : ℝ
  heightScaleReadout : ℝ
  displayedTimeSeconds : ℝ
  showsLabel : PulseFigureLabel → Bool

/-!
The independent physical and scalar quantities in the pulse model.
`translationCoefficientCmPerSecond` is the coefficient printed in the phase
argument; it is kept separate from the physical `propagationSpeed`. Their
connection is supplied only by the governing laws below.
-/
structure TravelingPulseSetup where
  initialProfileHeightReadout : ℝ → ℝ
  pulseHeightReadout : ℝ → ℝ → ℝ
  translationCoefficientCmPerSecond : ℝ
  propagationSpeed : SpeedQuantity
  propagationDirection : HorizontalDirection
  crestPositionCm : ℝ → ℝ
  figure : PulseFigure

/-- The piecewise-linear scalar profile encoded by the three marked positions. -/
def triangularPulseProfile
    (heightScale leftFoot peakPosition rightFoot x : ℝ) : ℝ :=
  if x ≤ leftFoot then 0
  else if x ≤ peakPosition then
    heightScale * (x - leftFoot) / (peakPosition - leftFoot)
  else if x ≤ rightFoot then
    heightScale * (rightFoot - x) / (rightFoot - peakPosition)
  else 0

/-!
Problem-text and primary-raster readouts. In particular,
`translationCoefficient` records the given `5.0` in `h(x - 5.0 t)`; it does
not assert the requested physical speed. The right foot is `x = 4` in the
raster, while `x = 5` is only the right end of the displayed horizontal axis.
-/
structure MatchesProblemAndFigureReadouts
    (setup : TravelingPulseSetup) : Prop where
  horizontalUnit :
    setup.figure.horizontalAxisUnit = LengthUnit.centimeters
  timeUnit : setup.figure.timeUnit = TimeUnit.seconds
  allLabelsShown : ∀ label, setup.figure.showsLabel label = true
  horizontalAxisMinimum : setup.figure.horizontalAxisMinimumCm = 0
  horizontalAxisMaximum : setup.figure.horizontalAxisMaximumCm = 5
  verticalAxisMinimum : setup.figure.verticalAxisMinimumReadout = 0
  leftFoot : setup.figure.leftFootCm = 1
  peakPosition : setup.figure.peakPositionCm = 3
  rightFoot : setup.figure.rightFootCm = 4
  heightScale : setup.figure.heightScaleReadout = 2
  displayedAtInitialTime : setup.figure.displayedTimeSeconds = 0
  translationCoefficient : setup.translationCoefficientCmPerSecond = 5
  rightTravel : setup.propagationDirection = .right
  initialProfileFromRaster :
    ∀ xCm,
      setup.initialProfileHeightReadout xCm =
        triangularPulseProfile
          setup.figure.heightScaleReadout
          setup.figure.leftFootCm
          setup.figure.peakPositionCm
          setup.figure.rightFootCm
          xCm

/-!
The governing translated-profile law supplied by the expression
`h(x - 5t)`. It uses the independently stored phase coefficient and does not
assert a numerical value for the physical propagation speed.
-/
structure ObeysTranslatedPulseLaw (setup : TravelingPulseSetup) : Prop where
  translatedProfile :
    ∀ (xCm tSeconds : ℝ),
      setup.pulseHeightReadout xCm tSeconds =
        setup.initialProfileHeightReadout
          (xCm - setup.translationCoefficientCmPerSecond * tSeconds)

/-!
General constant-speed crest kinematics. The crest is characterized by the
displayed scale height, and its axial displacement is signed physical speed
times elapsed time. This law does not identify the speed with the translation
coefficient or with `5`.
-/
structure HasConstantSpeedCrestKinematics
    (setup : TravelingPulseSetup) : Prop where
  crestHasScaleHeight :
    ∀ tSeconds,
      setup.pulseHeightReadout (setup.crestPositionCm tSeconds) tSeconds =
        setup.figure.heightScaleReadout
  scaleHeightOnlyAtCrest :
    ∀ (xCm tSeconds : ℝ),
      setup.pulseHeightReadout xCm tSeconds =
          setup.figure.heightScaleReadout →
        xCm = setup.crestPositionCm tSeconds
  constantSpeedMotion :
    ∀ tSeconds,
      setup.crestPositionCm tSeconds =
        setup.crestPositionCm 0 +
          directionSign setup.propagationDirection *
            speedInCentimetersPerSecond setup.propagationSpeed * tSeconds

/-! ## Displayed choices and target -/

/-- The four displayed multiple-choice alternatives. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical speed readout printed beside each answer choice, in cm/s. -/
def answerChoiceSpeedInCentimetersPerSecond : AnswerChoice → ℝ
  | .A => 4.2
  | .B => 4.5
  | .C => 4.7
  | .D => 5.0

/--
For the given translated pulse, the physical propagation speed is `5 cm/s`,
which is answer choice D.
-/
theorem pulse_travel_speed
    (setup : TravelingPulseSetup)
    (readouts : MatchesProblemAndFigureReadouts setup)
    (translationLaw : ObeysTranslatedPulseLaw setup)
    (crestKinematics : HasConstantSpeedCrestKinematics setup) :
    speedInCentimetersPerSecond setup.propagationSpeed = 5 ∧
      answerChoiceSpeedInCentimetersPerSecond .D =
        speedInCentimetersPerSecond setup.propagationSpeed := by
  have pulseAtInitialCrest :
      setup.pulseHeightReadout 3 0 = setup.figure.heightScaleReadout := by
    rw [translationLaw.translatedProfile, readouts.initialProfileFromRaster]
    norm_num [readouts.translationCoefficient, readouts.heightScale,
      readouts.leftFoot, readouts.peakPosition, readouts.rightFoot,
      triangularPulseProfile]
  have initialCrestPosition : (3 : ℝ) = setup.crestPositionCm 0 :=
    crestKinematics.scaleHeightOnlyAtCrest 3 0 pulseAtInitialCrest
  have pulseAtTranslatedCrest :
      setup.pulseHeightReadout 8 1 = setup.figure.heightScaleReadout := by
    rw [translationLaw.translatedProfile, readouts.initialProfileFromRaster]
    norm_num [readouts.translationCoefficient, readouts.heightScale,
      readouts.leftFoot, readouts.peakPosition, readouts.rightFoot,
      triangularPulseProfile]
  have translatedCrestPosition : (8 : ℝ) = setup.crestPositionCm 1 :=
    crestKinematics.scaleHeightOnlyAtCrest 8 1 pulseAtTranslatedCrest
  have motionAtOneSecond := crestKinematics.constantSpeedMotion 1
  rw [← translatedCrestPosition, ← initialCrestPosition,
    readouts.rightTravel] at motionAtOneSecond
  norm_num [directionSign] at motionAtOneSecond
  have speedIsFive :
      speedInCentimetersPerSecond setup.propagationSpeed = 5 := by
    linarith
  constructor
  · exact speedIsFive
  · norm_num [answerChoiceSpeedInCentimetersPerSecond, speedIsFive]

end PhyXMiniProblems.ProblemPhyXMini0301
