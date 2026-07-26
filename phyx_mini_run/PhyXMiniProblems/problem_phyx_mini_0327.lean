import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0327

open Dimension

/-!
# Speed of an approaching target from a reflected sound wave

The figure shows a transmitter labelled `f_s` and a receiver labelled `f_r`
in one instrument at the left. A wave travels right to a flat target moving
left toward the instrument with speed `u`; the reflected wave returns left.

The echo undergoes two acoustic Doppler shifts. On the outbound leg the moving
target is the observer. Ideal reflection preserves frequency in the target's
rest frame, after which the target acts as a moving source on the return leg.

Frequencies and speed magnitudes are unit-independent Physlib quantities.
Real scalars below are used only for named-unit readouts, signed
one-dimensional components, figure coordinates, and displayed answer values.
-/

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

/-- Kilohertz readout of a physical frequency. -/
def frequencyInKilohertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyInHertz frequency / 1000

/-- Meters-per-second readout of a physical speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Physical bodies in the one-dimensional echo experiment. -/
inductive PhysicalObject where
  | instrument
  | target
  deriving DecidableEq, Repr

/-- Labels visible in the supplied figure. -/
inductive FigureLabel where
  | transmittedFrequencyFs
  | receivedFrequencyFr
  | targetVelocityU
  | target
  deriving DecidableEq, Repr

/-- Horizontal directions in the supplied image. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- One-dimensional motion with physical speed magnitude and direction. -/
structure HorizontalMotion where
  speedMagnitude : SpeedQuantity
  direction : HorizontalDirection

/-- Signed SI velocity component, positive toward the right of the figure. -/
def signedVelocityInMetersPerSecond (motion : HorizontalMotion) : ℝ :=
  match motion.direction with
  | .left => -speedInMetersPerSecond motion.speedMagnitude
  | .right => speedInMetersPerSecond motion.speedMagnitude

/-- Propagation sign along the same right-positive horizontal axis. -/
def propagationSign : HorizontalDirection → ℝ
  | .left => -1
  | .right => 1

/-!
Qualitative information read directly from the primary bitmap. Pixel
coordinates record only left-to-right ordering, not physical distances.
-/
structure EchoSpeedFigure where
  labelPositionFromLeftPixels : FigureLabel → ℝ
  outboundArrowDirection : HorizontalDirection
  returnArrowDirection : HorizontalDirection
  targetVelocityArrowDirection : HorizontalDirection
  transmitterAndReceiverShownInOneInstrument : Bool
  targetShownAsFlatPlate : Bool
  emittedFrequencyLabelShown : Bool
  receivedFrequencyLabelShown : Bool
  targetVelocityLabelShown : Bool

/-!
Independent physical quantities for the emitted, incident, reflected, and
detected waves. In particular, the unknown target speed is not defined by an
answer choice, and the intermediate frequencies are related only by the
governing-law premises below.
-/
structure MovingTargetEchoSetup where
  motion : PhysicalObject → HorizontalMotion
  airMotion : HorizontalMotion
  physicalPositionFromLeftMeters : PhysicalObject → ℝ
  soundSpeedInAir : SpeedQuantity
  emittedFrequency : FrequencyQuantity
  incidentFrequencyInTargetFrame : FrequencyQuantity
  reflectedFrequencyInTargetFrame : FrequencyQuantity
  detectedReturnFrequency : FrequencyQuantity
  outboundPropagationDirection : HorizontalDirection
  returnPropagationDirection : HorizontalDirection
  transmitterAndReceiverShareInstrument : Bool
  targetIsIdealizedFlatPlate : Bool
  targetMovesDirectlyTowardInstrument : Bool
  figure : EchoSpeedFigure

/-!
Primary-image evidence: `f_s` and `f_r` are at the left of the target, the
outbound arrow points right, the return arrow points left, and the target's
`u` arrow points left. The bitmap also depicts a shared instrument and a flat
target plate.
-/
structure MatchesPrimaryFigure (setup : MovingTargetEchoSetup) : Prop where
  emittedFrequencyLabelLeftOfTarget :
    setup.figure.labelPositionFromLeftPixels .transmittedFrequencyFs <
      setup.figure.labelPositionFromLeftPixels .target
  receivedFrequencyLabelLeftOfTarget :
    setup.figure.labelPositionFromLeftPixels .receivedFrequencyFr <
      setup.figure.labelPositionFromLeftPixels .target
  velocityLabelNearTarget :
    setup.figure.labelPositionFromLeftPixels .targetVelocityU <
      setup.figure.labelPositionFromLeftPixels .target
  outboundArrowPointsRight :
    setup.figure.outboundArrowDirection = .right
  returnArrowPointsLeft :
    setup.figure.returnArrowDirection = .left
  targetVelocityArrowPointsLeft :
    setup.figure.targetVelocityArrowDirection = .left
  sharedInstrumentShown :
    setup.figure.transmitterAndReceiverShownInOneInstrument = true
  flatTargetShown : setup.figure.targetShownAsFlatPlate = true
  emittedLabelShown : setup.figure.emittedFrequencyLabelShown = true
  receivedLabelShown : setup.figure.receivedFrequencyLabelShown = true
  velocityLabelShown : setup.figure.targetVelocityLabelShown = true

/-!
Problem-statement readouts and geometry. The source emits at `18.0 kHz`, the
receiver detects the returning wave at `22.2 kHz`, the combined instrument is
stationary, and the target approaches it head-on. This predicate contains no
value for the requested target speed.
-/
structure MatchesProblemReadouts (setup : MovingTargetEchoSetup) : Prop where
  emittedFrequencyKilohertz :
    frequencyInKilohertz setup.emittedFrequency = 18
  detectedFrequencyKilohertz :
    frequencyInKilohertz setup.detectedReturnFrequency = 111 / 5
  instrumentStationary :
    speedInMetersPerSecond
        (setup.motion .instrument).speedMagnitude = 0
  targetMovesLeft : (setup.motion .target).direction = .left
  instrumentLeftOfTarget :
    setup.physicalPositionFromLeftMeters .instrument <
      setup.physicalPositionFromLeftMeters .target
  outboundSoundMovesRight :
    setup.outboundPropagationDirection = .right
  returnSoundMovesLeft :
    setup.returnPropagationDirection = .left
  sharedTransmitterAndReceiver :
    setup.transmitterAndReceiverShareInstrument = true
  flatPlateTarget : setup.targetIsIdealizedFlatPlate = true
  headOnApproach : setup.targetMovesDirectlyTowardInstrument = true

/-!
The stem does not print the acoustic propagation speed or mention wind. The
recorded answer uses the conventional room-temperature still-air calibration
`343 m/s`; it is exposed as a separate model input rather than attributed to
the figure or hidden in a definition.
-/
structure HasStandardStillAirCalibration
    (setup : MovingTargetEchoSetup) : Prop where
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeedInAir = 343
  stillAir : speedInMetersPerSecond setup.airMotion.speedMagnitude = 0

/-!
Positivity and subsonic conditions under which the classical acoustic Doppler
relations are physically meaningful.
-/
structure HasPhysicalAcousticParameters
    (setup : MovingTargetEchoSetup) : Prop where
  emittedFrequencyPositive :
    0 < frequencyInHertz setup.emittedFrequency
  incidentFrequencyPositive :
    0 < frequencyInHertz setup.incidentFrequencyInTargetFrame
  reflectedFrequencyPositive :
    0 < frequencyInHertz setup.reflectedFrequencyInTargetFrame
  detectedFrequencyPositive :
    0 < frequencyInHertz setup.detectedReturnFrequency
  soundSpeedPositive :
    0 < speedInMetersPerSecond setup.soundSpeedInAir
  targetSubsonicRelativeToAir :
    |signedVelocityInMetersPerSecond (setup.motion .target) -
        signedVelocityInMetersPerSecond setup.airMotion| <
      speedInMetersPerSecond setup.soundSpeedInAir

/-!
The classical one-dimensional acoustic Doppler law on the two path legs. For
propagation sign `q`, source velocity `v_s`, observer velocity `v_o`, air
velocity `v_a`, and sound speed `c`, the multiplicative factor is
`(c - q * (v_o - v_a)) / (c - q * (v_s - v_a))`.

On the outbound leg the stationary instrument emits and the moving target
observes. On the return leg the moving target emits in its rest frame and the
stationary instrument observes. These are governing relations and contain no
requested answer value.
-/
structure SatisfiesTwoLegAcousticDopplerLaw
    (setup : MovingTargetEchoSetup) : Prop where
  outboundLeg :
    frequencyInHertz setup.incidentFrequencyInTargetFrame =
      frequencyInHertz setup.emittedFrequency *
        (speedInMetersPerSecond setup.soundSpeedInAir -
          propagationSign setup.outboundPropagationDirection *
            (signedVelocityInMetersPerSecond (setup.motion .target) -
              signedVelocityInMetersPerSecond setup.airMotion)) /
        (speedInMetersPerSecond setup.soundSpeedInAir -
          propagationSign setup.outboundPropagationDirection *
            (signedVelocityInMetersPerSecond (setup.motion .instrument) -
              signedVelocityInMetersPerSecond setup.airMotion))
  returnLeg :
    frequencyInHertz setup.detectedReturnFrequency =
      frequencyInHertz setup.reflectedFrequencyInTargetFrame *
        (speedInMetersPerSecond setup.soundSpeedInAir -
          propagationSign setup.returnPropagationDirection *
            (signedVelocityInMetersPerSecond (setup.motion .instrument) -
              signedVelocityInMetersPerSecond setup.airMotion)) /
        (speedInMetersPerSecond setup.soundSpeedInAir -
          propagationSign setup.returnPropagationDirection *
            (signedVelocityInMetersPerSecond (setup.motion .target) -
              signedVelocityInMetersPerSecond setup.airMotion))

/-!
Ideal reflection from the flat plate preserves the incident frequency in the
target's rest frame. It relates two independent frequency quantities and does
not state the target speed.
-/
structure SatisfiesIdealReflectionInTargetFrame
    (setup : MovingTargetEchoSetup) : Prop where
  reflectedEqualsIncidentInTargetFrame :
    frequencyInHertz setup.reflectedFrequencyInTargetFrame =
      frequencyInHertz setup.incidentFrequencyInTargetFrame

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Speed in meters per second printed beside each answer label. -/
def displayedAnswerSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 1623 / 50
  | .B => 1679 / 50
  | .C => 869 / 25
  | .D => 896 / 25

/-- The answer label recorded in the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A physical speed readout rounds to the displayed hundredth of a meter per
second when it lies strictly within `0.005 m/s` of that value.
-/
def RoundsToNearestHundredthMeterPerSecond
    (speed : SpeedQuantity) (displayedSpeed : ℝ) : Prop :=
  |speedInMetersPerSecond speed - displayedSpeed| < (1 / 200 : ℝ)

/-- The modeled target speed agrees, after rounding, with an answer choice. -/
def MatchesAnswerChoice
    (setup : MovingTargetEchoSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredthMeterPerSecond
    (setup.motion .target).speedMagnitude
    (displayedAnswerSpeedInMetersPerSecond choice)

/-!
Solving the two-leg Doppler relation for the approaching target speed gives
`343 * (22.2 - 18.0) / (22.2 + 18.0)` meters per second. This is the
unrounded physical-model result.
-/
lemma targetSpeed_doppler_readout
    (setup : MovingTargetEchoSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemReadouts setup)
    (hCalibration : HasStandardStillAirCalibration setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hDoppler : SatisfiesTwoLegAcousticDopplerLaw setup)
    (hReflection : SatisfiesIdealReflectionInTargetFrame setup) :
    speedInMetersPerSecond (setup.motion .target).speedMagnitude =
      343 * ((111 / 5 : ℝ) - 18) / ((111 / 5 : ℝ) + 18) := by
  have hEmitted := hProblem.emittedFrequencyKilohertz
  rw [frequencyInKilohertz] at hEmitted
  have hEmittedHertz :
      frequencyInHertz setup.emittedFrequency = 18000 := by
    linarith
  have hDetected := hProblem.detectedFrequencyKilohertz
  rw [frequencyInKilohertz] at hDetected
  have hDetectedHertz :
      frequencyInHertz setup.detectedReturnFrequency = 22200 := by
    linarith
  have hInstrumentVelocity :
      signedVelocityInMetersPerSecond (setup.motion .instrument) = 0 := by
    cases hDirection : (setup.motion .instrument).direction <;>
      simp [signedVelocityInMetersPerSecond, hDirection,
        hProblem.instrumentStationary]
  have hTargetVelocity :
      signedVelocityInMetersPerSecond (setup.motion .target) =
        -speedInMetersPerSecond (setup.motion .target).speedMagnitude := by
    simp [signedVelocityInMetersPerSecond, hProblem.targetMovesLeft]
  have hAirVelocity :
      signedVelocityInMetersPerSecond setup.airMotion = 0 := by
    cases hDirection : setup.airMotion.direction <;>
      simp [signedVelocityInMetersPerSecond, hDirection,
        hCalibration.stillAir]
  have hOutbound := hDoppler.outboundLeg
  have hReturn := hDoppler.returnLeg
  have hReflect :=
    hReflection.reflectedEqualsIncidentInTargetFrame
  norm_num [hProblem.outboundSoundMovesRight, propagationSign,
    hCalibration.soundSpeedMetersPerSecond,
    hInstrumentVelocity, hTargetVelocity, hAirVelocity] at hOutbound
  norm_num [hProblem.returnSoundMovesLeft, propagationSign,
    hCalibration.soundSpeedMetersPerSecond,
    hInstrumentVelocity, hTargetVelocity, hAirVelocity] at hReturn
  rw [hReflect, hOutbound] at hReturn
  have hSubsonic := hPhysical.targetSubsonicRelativeToAir
  rw [hTargetVelocity, hAirVelocity,
    hCalibration.soundSpeedMetersPerSecond] at hSubsonic
  rw [abs_lt] at hSubsonic
  have hDenominator :
      343 -
          speedInMetersPerSecond (setup.motion .target).speedMagnitude ≠
        0 := by
    linarith
  field_simp [hDenominator] at hReturn
  rw [hEmittedHertz, hDetectedHertz] at hReturn
  norm_num at hReturn ⊢
  linarith

/-!
The exact ideal-model speed is `2401/67 m/s`, approximately `35.8358 m/s`,
and therefore rounds to `35.84 m/s`, answer choice D.

This formalizes `thm:physics:phyx_mini_0327:target`.
-/
theorem problem_phyx_mini_0327
    (setup : MovingTargetEchoSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemReadouts setup)
    (hCalibration : HasStandardStillAirCalibration setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hDoppler : SatisfiesTwoLegAcousticDopplerLaw setup)
    (hReflection : SatisfiesIdealReflectionInTargetFrame setup) :
    speedInMetersPerSecond (setup.motion .target).speedMagnitude = 2401 / 67 ∧
      RoundsToNearestHundredthMeterPerSecond
        (setup.motion .target).speedMagnitude (896 / 25) ∧
      MatchesAnswerChoice setup .D := by
  have hSpeed :=
    targetSpeed_doppler_readout setup hFigure hProblem
      hCalibration hPhysical hDoppler hReflection
  constructor
  · calc
      speedInMetersPerSecond (setup.motion .target).speedMagnitude =
          343 * ((111 / 5 : ℝ) - 18) / ((111 / 5 : ℝ) + 18) := hSpeed
      _ = 2401 / 67 := by norm_num
  constructor
  · rw [RoundsToNearestHundredthMeterPerSecond, hSpeed]
    norm_num [abs_of_nonneg, abs_of_neg]
  · rw [MatchesAnswerChoice, displayedAnswerSpeedInMetersPerSecond,
      RoundsToNearestHundredthMeterPerSecond, hSpeed]
    norm_num [abs_of_nonneg, abs_of_neg]

end PhyXMiniProblems.ProblemPhyXMini0327
