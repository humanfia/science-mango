import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0214

open Dimension

/-!
# Sound reflected from an approaching object

A stationary source emits a `5000 Hz` sound wave toward an object to its
right.  The primary figure shows the wave traveling right and the object
moving left, toward the source, at `3.50 m/s`.  A stationary detector near the
source receives the reflected wave.

There are two acoustic Doppler shifts.  On the outbound leg the moving object
is the observer.  Ideal reflection preserves frequency in the object's rest
frame, after which the object acts as a moving source on the return leg.

Frequency and speed magnitudes are unit-independent Physlib quantities.  Real
scalars below are reserved for named-unit readouts, signed one-dimensional
components, figure coordinates, and displayed answer values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical frequency carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical frequency in inverse units of a selected time unit. -/
def frequencyReadout
    (timeUnit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meters-per-second readout of a physical speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Bodies, directions, and primary-figure data -/

/-- Physical bodies occurring in the prose scenario. -/
inductive PhysicalObject where
  | originalSource
  | reflectingObject
  | detector
  deriving DecidableEq, Repr

/-- The two object labels printed in the supplied bitmap. -/
inductive FigureLabel where
  | originalSource
  | object
  deriving DecidableEq, Repr

/-- Horizontal directions in the supplied image. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- One-dimensional motion with dimensionful speed magnitude and direction. -/
structure HorizontalMotion where
  speedMagnitude : SpeedQuantity
  direction : HorizontalDirection

/--
Signed velocity readout, positive toward the right of the figure, in selected
length and time units.
-/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (motion : HorizontalMotion) : ℝ :=
  match motion.direction with
  | .left => -speedReadout lengthUnit timeUnit motion.speedMagnitude
  | .right => speedReadout lengthUnit timeUnit motion.speedMagnitude

/-- Signed SI velocity component, positive toward the right of the figure. -/
def signedVelocityInMetersPerSecond (motion : HorizontalMotion) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds motion

/-- Propagation sign along the same right-positive horizontal axis. -/
def propagationSign : HorizontalDirection → ℝ
  | .left => -1
  | .right => 1

/-!
Qualitative and quantitative information read directly from the primary
figure.  Pixel coordinates preserve only ordering, not physical distance.
The detector belongs to the prose scenario and is not drawn in this image.
-/
structure MovingReflectorFigure where
  labelPositionFromLeftPixels : FigureLabel → ℝ
  waveVelocityArrowDirection : HorizontalDirection
  observerVelocityArrowDirection : HorizontalDirection
  observerVelocityLabelMetersPerSecond : ℝ
  showsWavefrontsBetweenSourceAndObject : Bool
  showsDetector : Bool

/-!
Independent physical quantities for the emitted, incident, reflected, and
detected waves.  In particular, the detected frequency is not defined from
the Doppler formula or from an answer choice; the governing laws below relate
it to the other quantities.
-/
structure MovingObjectReflectionSetup where
  motion : PhysicalObject → HorizontalMotion
  airMotion : HorizontalMotion
  physicalPositionFromLeftMeters : PhysicalObject → ℝ
  soundSpeedInAir : SpeedQuantity
  emittedFrequency : FrequencyQuantity
  incidentFrequencyInObjectFrame : FrequencyQuantity
  reflectedFrequencyInObjectFrame : FrequencyQuantity
  detectedReflectedFrequency : FrequencyQuantity
  outboundPropagationDirection : HorizontalDirection
  returnPropagationDirection : HorizontalDirection
  objectActsAsReflector : Bool
  figure : MovingReflectorFigure

/-!
Primary-image evidence: the original source is left of the object; the wave
velocity arrow points right; the object's `v_obs` arrow points left and is
labelled `3.50 m/s`; wavefronts are drawn between them; no detector is drawn.
-/
structure MatchesPrimaryFigure
    (setup : MovingObjectReflectionSetup) : Prop where
  sourceLeftOfObjectInImage :
    setup.figure.labelPositionFromLeftPixels .originalSource <
      setup.figure.labelPositionFromLeftPixels .object
  waveArrowPointsRight :
    setup.figure.waveVelocityArrowDirection = .right
  observerArrowPointsLeft :
    setup.figure.observerVelocityArrowDirection = .left
  observerSpeedLabel :
    setup.figure.observerVelocityLabelMetersPerSecond = 7 / 2
  wavefrontsShown :
    setup.figure.showsWavefrontsBetweenSourceAndObject = true
  detectorNotDrawn : setup.figure.showsDetector = false

/-!
Problem-statement readouts and geometry.  The source emits at `5000 Hz`; the
reflecting object approaches at `3.50 m/s`; source and detector are at rest;
and the detector lies nearer the source than the reflecting object does.  No
value of the requested detected frequency occurs here.
-/
structure MatchesProblemReadouts
    (setup : MovingObjectReflectionSetup) : Prop where
  emittedFrequencyHertz :
    frequencyInHertz setup.emittedFrequency = 5000
  sourceStationary :
    speedInMetersPerSecond
        (setup.motion .originalSource).speedMagnitude = 0
  objectSpeedMetersPerSecond :
    speedInMetersPerSecond
        (setup.motion .reflectingObject).speedMagnitude = 7 / 2
  objectMovesLeft :
    (setup.motion .reflectingObject).direction = .left
  detectorStationary :
    speedInMetersPerSecond (setup.motion .detector).speedMagnitude = 0
  sourceLeftOfReflector :
    setup.physicalPositionFromLeftMeters .originalSource <
      setup.physicalPositionFromLeftMeters .reflectingObject
  detectorNearSource :
    |setup.physicalPositionFromLeftMeters .detector -
        setup.physicalPositionFromLeftMeters .originalSource| <
      |setup.physicalPositionFromLeftMeters .reflectingObject -
        setup.physicalPositionFromLeftMeters .originalSource|
  outboundSoundMovesRight :
    setup.outboundPropagationDirection = .right
  reflectedSoundMovesLeft :
    setup.returnPropagationDirection = .left
  objectReflectsSound : setup.objectActsAsReflector = true

/-!
The stem does not print the sound speed or mention wind.  The recorded answer
uses the conventional room-temperature still-air calibration `343 m/s`, so
that calibration is exposed as a separate input rather than attributed to the
figure or hidden in a definition.
-/
structure HasStandardStillAirCalibration
    (setup : MovingObjectReflectionSetup) : Prop where
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeedInAir = 343
  stillAir :
    speedInMetersPerSecond setup.airMotion.speedMagnitude = 0

/-!
Positivity and subsonic conditions under which the classical acoustic Doppler
relations are physically meaningful.
-/
structure HasPhysicalAcousticParameters
    (setup : MovingObjectReflectionSetup) : Prop where
  emittedFrequencyPositive :
    0 < frequencyInHertz setup.emittedFrequency
  incidentFrequencyPositive :
    0 < frequencyInHertz setup.incidentFrequencyInObjectFrame
  reflectedFrequencyPositive :
    0 < frequencyInHertz setup.reflectedFrequencyInObjectFrame
  detectedFrequencyPositive :
    0 < frequencyInHertz setup.detectedReflectedFrequency
  soundSpeedPositive :
    0 < speedInMetersPerSecond setup.soundSpeedInAir
  reflectorSubsonicRelativeToAir :
    |signedVelocityInMetersPerSecond (setup.motion .reflectingObject) -
        signedVelocityInMetersPerSecond setup.airMotion| <
      speedInMetersPerSecond setup.soundSpeedInAir

/-! ## Governing acoustic laws -/

/-!
The classical one-dimensional acoustic Doppler relation on the two path legs.
For propagation sign `q`, source velocity `v_s`, observer velocity `v_o`, air
velocity `v_a`, and sound speed `c`, the multiplicative factor is

`(c - q * (v_o - v_a)) / (c - q * (v_s - v_a))`.

On the outbound leg the original source emits and the object observes.  On
the return leg the object emits in its rest frame and the detector observes.
The laws hold in every compatible choice of length and time units and contain
no requested answer value.
-/
structure SatisfiesTwoLegAcousticDopplerLaw
    (setup : MovingObjectReflectionSetup) : Prop where
  outboundLeg :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      frequencyReadout timeUnit setup.incidentFrequencyInObjectFrame =
        frequencyReadout timeUnit setup.emittedFrequency *
          (speedReadout lengthUnit timeUnit setup.soundSpeedInAir -
            propagationSign setup.outboundPropagationDirection *
              (signedVelocityReadout lengthUnit timeUnit
                  (setup.motion .reflectingObject) -
                signedVelocityReadout lengthUnit timeUnit setup.airMotion)) /
          (speedReadout lengthUnit timeUnit setup.soundSpeedInAir -
            propagationSign setup.outboundPropagationDirection *
              (signedVelocityReadout lengthUnit timeUnit
                  (setup.motion .originalSource) -
                signedVelocityReadout lengthUnit timeUnit setup.airMotion))
  returnLeg :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      frequencyReadout timeUnit setup.detectedReflectedFrequency =
        frequencyReadout timeUnit setup.reflectedFrequencyInObjectFrame *
          (speedReadout lengthUnit timeUnit setup.soundSpeedInAir -
            propagationSign setup.returnPropagationDirection *
              (signedVelocityReadout lengthUnit timeUnit
                  (setup.motion .detector) -
                signedVelocityReadout lengthUnit timeUnit setup.airMotion)) /
          (speedReadout lengthUnit timeUnit setup.soundSpeedInAir -
            propagationSign setup.returnPropagationDirection *
              (signedVelocityReadout lengthUnit timeUnit
                  (setup.motion .reflectingObject) -
                signedVelocityReadout lengthUnit timeUnit setup.airMotion))

/-!
Ideal reflection preserves the incident frequency in the reflecting object's
rest frame.  This boundary law relates two independent frequency quantities;
it does not state the frequency later received by the detector.
-/
structure SatisfiesIdealReflectionInObjectFrame
    (setup : MovingObjectReflectionSetup) : Prop where
  reflectedEqualsIncidentInObjectFrame :
    ∀ timeUnit : TimeUnit,
      frequencyReadout timeUnit setup.reflectedFrequencyInObjectFrame =
        frequencyReadout timeUnit setup.incidentFrequencyInObjectFrame

/-! ## Displayed answers and formalization target -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Whole-hertz value printed beside each answer label. -/
def displayedAnswerFrequencyInHertz : AnswerChoice → ℝ
  | .A => 5152
  | .B => 5051
  | .C => 5203
  | .D => 5103

/-- The answer label recorded in the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A physical frequency readout rounds to the displayed whole-hertz value when
it lies strictly within half a hertz of that value.
-/
def RoundsToNearestHertz
    (frequency : FrequencyQuantity) (nearestWholeHertz : ℝ) : Prop :=
  |frequencyInHertz frequency - nearestWholeHertz| < (1 / 2 : ℝ)

/-- The modeled reflected wave agrees with a displayed answer choice. -/
def MatchesAnswerChoice
    (setup : MovingObjectReflectionSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHertz setup.detectedReflectedFrequency
    (displayedAnswerFrequencyInHertz choice)

/-!
The two Doppler shifts and rest-frame reflection law give the unrounded
double-shifted readout
`5000 * (343 + 7/2) / (343 - 7/2)` hertz.
-/
lemma detectedReflectedFrequency_doppler_readout
    (setup : MovingObjectReflectionSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemReadouts setup)
    (hCalibration : HasStandardStillAirCalibration setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hDoppler : SatisfiesTwoLegAcousticDopplerLaw setup)
    (hReflection : SatisfiesIdealReflectionInObjectFrame setup) :
    frequencyInHertz setup.detectedReflectedFrequency =
      5000 * (343 + 7 / 2) / (343 - 7 / 2) := by
  have hEmitted :
      frequencyReadout TimeUnit.seconds setup.emittedFrequency = 5000 :=
    hProblem.emittedFrequencyHertz
  have hSourceSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
        (setup.motion .originalSource).speedMagnitude = 0 :=
    hProblem.sourceStationary
  have hObjectSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
        (setup.motion .reflectingObject).speedMagnitude = 7 / 2 :=
    hProblem.objectSpeedMetersPerSecond
  have hDetectorSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
        (setup.motion .detector).speedMagnitude = 0 :=
    hProblem.detectorStationary
  have hSoundSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds setup.soundSpeedInAir =
        343 :=
    hCalibration.soundSpeedMetersPerSecond
  have hAirSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
        setup.airMotion.speedMagnitude = 0 :=
    hCalibration.stillAir
  have hSourceVelocity :
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
        (setup.motion .originalSource) = 0 := by
    cases hDirection : (setup.motion .originalSource).direction <;>
      simp [signedVelocityReadout, hDirection, hSourceSpeed]
  have hObjectVelocity :
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
        (setup.motion .reflectingObject) = -(7 / 2) := by
    simp [signedVelocityReadout, hProblem.objectMovesLeft, hObjectSpeed]
  have hDetectorVelocity :
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
        (setup.motion .detector) = 0 := by
    cases hDirection : (setup.motion .detector).direction <;>
      simp [signedVelocityReadout, hDirection, hDetectorSpeed]
  have hAirVelocity :
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
        setup.airMotion = 0 := by
    cases hDirection : setup.airMotion.direction <;>
      simp [signedVelocityReadout, hDirection, hAirSpeed]
  have hOutbound :=
    hDoppler.outboundLeg LengthUnit.meters TimeUnit.seconds
  have hReturn :=
    hDoppler.returnLeg LengthUnit.meters TimeUnit.seconds
  have hReflect :=
    hReflection.reflectedEqualsIncidentInObjectFrame TimeUnit.seconds
  simp [hProblem.outboundSoundMovesRight, propagationSign,
    hEmitted, hSoundSpeed,
    hSourceVelocity, hObjectVelocity, hAirVelocity] at hOutbound
  simp [hProblem.reflectedSoundMovesLeft, propagationSign,
    hSoundSpeed, hDetectorVelocity,
    hObjectVelocity, hAirVelocity] at hReturn
  rw [hReflect, hOutbound] at hReturn
  change frequencyReadout TimeUnit.seconds setup.detectedReflectedFrequency =
    5000 * (343 + 7 / 2) / (343 - 7 / 2)
  norm_num at hReturn ⊢
  exact hReturn

/-!
The exact ideal-model readout is `495000 / 97` hertz, approximately
`5103.093 Hz`, and therefore rounds to `5103 Hz`, answer choice D.

This formalizes `thm:physics:phyx_mini_0214:target`.
-/
theorem problem_phyx_mini_0214
    (setup : MovingObjectReflectionSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemReadouts setup)
    (hCalibration : HasStandardStillAirCalibration setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hDoppler : SatisfiesTwoLegAcousticDopplerLaw setup)
    (hReflection : SatisfiesIdealReflectionInObjectFrame setup) :
    frequencyInHertz setup.detectedReflectedFrequency = 495000 / 97 ∧
      RoundsToNearestHertz setup.detectedReflectedFrequency 5103 ∧
      MatchesAnswerChoice setup .D := by
  have hDetected :=
    detectedReflectedFrequency_doppler_readout setup hFigure hProblem
      hCalibration hPhysical hDoppler hReflection
  constructor
  · calc
      frequencyInHertz setup.detectedReflectedFrequency =
          5000 * (343 + 7 / 2) / (343 - 7 / 2) := hDetected
      _ = 495000 / 97 := by norm_num
  constructor
  · rw [RoundsToNearestHertz, hDetected]
    norm_num [abs_of_nonneg, abs_of_neg]
  · rw [MatchesAnswerChoice, displayedAnswerFrequencyInHertz,
      RoundsToNearestHertz, hDetected]
    norm_num [abs_of_nonneg, abs_of_neg]

end PhyXMiniProblems.ProblemPhyXMini0214
