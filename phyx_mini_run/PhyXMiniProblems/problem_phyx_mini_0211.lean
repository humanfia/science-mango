import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Ultrasonic autofocus pulse round-trip time

An autofocus camera sends an ultrasonic pulse from the camera to a photographed
subject and detects the reflected pulse back at a sensor in the camera.  The
primary image places the camera on the left and the subject on the right, with
arrows in both directions.  Hence an object `20 m` away gives two propagation
legs of equal length.

Lengths, positions, durations, frequencies, and sound speed are represented by
unit-independent Physlib quantities.  Real numbers below occur only as readouts
in explicitly named units and as the numerical values printed in the answer
table.

Assumption/target split:

* `MatchesPrimaryFigure` records the apparatus roles and out-and-back geometry;
* `HasStatedObjectDistance` records the given one-way distance `20 m`;
* `EmitsUltrasonicPulse` records the stated ultrasonic frequency band;
* `UsesStandardAirSoundSpeed` supplies the separate `340 m/s` calibration;
* `SatisfiesEchoPropagationLaws` states constant-speed propagation and time
  additivity;
* the exact and multiple-choice travel times occur only in the conclusions of
  `roundTripTravelTime_milliseconds_eq` and
  `roundTripTravelTime_matches_recordedChoiceD`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0211

open Dimension

/-! ## Dimensionful acoustic quantities and named-unit readouts -/

/-- A nonnegative physical acoustic-path length. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical axial position used to preserve the left-to-right figure geometry. -/
abbrev AxialPosition : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical propagation duration. -/
abbrev AcousticDuration : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical acoustic frequency, carrying inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The nonnegative dimensionful propagation speed supplied by Physlib. -/
abbrev AcousticSpeed : Type := DimSpeed

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed axial position in the selected length unit. -/
def positionReadout (unit : LengthUnit) (position : AxialPosition) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a physical duration in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : AcousticDuration) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in the selected coherent length-per-time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : AcousticSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout used for the camera-to-subject separation and both pulse legs. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre readout of a signed position along the image's horizontal axis. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  positionReadout LengthUnit.meters position

/-- Second readout used in the propagation law. -/
def durationInSeconds (duration : AcousticDuration) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Millisecond readout used by the four displayed answers. -/
def durationInMilliseconds (duration : AcousticDuration) : ℝ :=
  durationReadout TimeUnit.milliseconds duration

/-- Hertz readout used to express the stated ultrasonic character of the pulse. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Metres-per-second readout of the propagation speed in air. -/
def speedInMetersPerSecond (speed : AcousticSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Apparatus and primary-figure labels -/

/-- The camera, its two autofocus components, and the photographed subject. -/
inductive FigureObject where
  | cameraBody
  | ultrasonicEmitter
  | returnSensor
  | photographedSubject
  deriving DecidableEq, Repr

/-- The two legs of the pulse path shown by oppositely directed arrows. -/
inductive PulseLeg where
  | outbound
  | reflectedReturn
  deriving DecidableEq, Repr

/-- The two horizontal propagation directions in the primary image. -/
inductive AxialDirection where
  | cameraToSubject
  | subjectToCamera
  deriving DecidableEq, Repr

/--
The autofocus apparatus and its physical observables.

`roundTripTravelTime` is an unknown physical duration.  This structure assigns
it no numerical readout and does not select an answer choice.
-/
structure AutofocusEchoSetup where
  objectPosition : FigureObject → AxialPosition
  cameraSubjectSeparation : AcousticLength
  pulseEmitter : FigureObject
  pulseReflector : FigureObject
  pulseDetector : FigureObject
  pulseFrequency : AcousticFrequency
  soundSpeedInAir : AcousticSpeed
  pathLength : PulseLeg → AcousticLength
  legTravelTime : PulseLeg → AcousticDuration
  propagationDirection : PulseLeg → AxialDirection
  detectedPulse : PulseLeg → Bool
  roundTripTravelTime : AcousticDuration

/-!
Qualitative and geometric evidence from the problem text and primary image.
The emitter and detector are co-located with the camera, the subject is to the
right, and the emitted and reflected legs traverse the same separation in
opposite directions.  The sensor detects the returned leg.

No numerical travel-time readout or answer label occurs here.
-/
structure MatchesPrimaryFigure (setup : AutofocusEchoSetup) : Prop where
  emitterRole : setup.pulseEmitter = .ultrasonicEmitter
  reflectorRole : setup.pulseReflector = .photographedSubject
  detectorRole : setup.pulseDetector = .returnSensor
  emitterAtCamera :
    positionInMeters (setup.objectPosition .ultrasonicEmitter) =
      positionInMeters (setup.objectPosition .cameraBody)
  sensorAtCamera :
    positionInMeters (setup.objectPosition .returnSensor) =
      positionInMeters (setup.objectPosition .cameraBody)
  cameraLeftOfSubject :
    positionInMeters (setup.objectPosition .cameraBody) <
      positionInMeters (setup.objectPosition .photographedSubject)
  separationGeometry :
    positionInMeters (setup.objectPosition .photographedSubject) -
        positionInMeters (setup.objectPosition .cameraBody) =
      lengthInMeters setup.cameraSubjectSeparation
  outboundPathLength :
    lengthInMeters (setup.pathLength .outbound) =
      lengthInMeters setup.cameraSubjectSeparation
  reflectedReturnPathLength :
    lengthInMeters (setup.pathLength .reflectedReturn) =
      lengthInMeters setup.cameraSubjectSeparation
  outboundDirection :
    setup.propagationDirection .outbound = .cameraToSubject
  reflectedReturnDirection :
    setup.propagationDirection .reflectedReturn = .subjectToCamera
  sensorDetectsReturnedPulse :
    setup.detectedPulse .reflectedReturn = true

/-- The object's stated one-way distance from the camera is `20 m`. -/
def HasStatedObjectDistance (setup : AutofocusEchoSetup) : Prop :=
  lengthInMeters setup.cameraSubjectSeparation = 20

/-- Conventional lower-edge characterization of an ultrasonic frequency. -/
def IsUltrasonic (frequency : AcousticFrequency) : Prop :=
  20000 ≤ frequencyInHertz frequency

/-- The emitted autofocus pulse is ultrasonic, as stated in the scenario. -/
def EmitsUltrasonicPulse (setup : AutofocusEchoSetup) : Prop :=
  IsUltrasonic setup.pulseFrequency

/-!
The standard textbook calibration `340 m/s` used to evaluate the answer
choices.  The supplied question does not print air temperature or sound speed,
so this datum is kept separate from the figure and propagation law.
-/
def UsesStandardAirSoundSpeed (setup : AutofocusEchoSetup) : Prop :=
  speedInMetersPerSecond setup.soundSpeedInAir = 340

/-- Positivity conditions selecting a nondegenerate physical echo experiment. -/
structure HasPhysicalEchoParameters (setup : AutofocusEchoSetup) : Prop where
  separationPositive :
    0 < lengthInMeters setup.cameraSubjectSeparation
  pulseFrequencyPositive :
    0 < frequencyInHertz setup.pulseFrequency
  soundSpeedPositive :
    0 < speedInMetersPerSecond setup.soundSpeedInAir
  pathLengthsPositive :
    ∀ leg, 0 < lengthInMeters (setup.pathLength leg)
  legTravelTimesNonnegative :
    ∀ leg, 0 ≤ durationInSeconds (setup.legTravelTime leg)
  roundTripTravelTimeNonnegative :
    0 ≤ durationInSeconds setup.roundTripTravelTime

/-!
The governing constant-speed and composition laws for the echo pulse.
Each homogeneous air leg obeys `distance = speed × time`, and the full
emission-to-detection duration is the sum of the outgoing and return durations.
Neither law contains `120 ms`, `2000/17 ms`, or an answer label.
-/
structure SatisfiesEchoPropagationLaws (setup : AutofocusEchoSetup) : Prop where
  constantSpeedPropagation : ∀ leg,
    speedInMetersPerSecond setup.soundSpeedInAir *
        durationInSeconds (setup.legTravelTime leg) =
      lengthInMeters (setup.pathLength leg)
  roundTripTimeComposition :
    durationInSeconds setup.roundTripTravelTime =
      durationInSeconds (setup.legTravelTime .outbound) +
        durationInSeconds (setup.legTravelTime .reflectedReturn)

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Millisecond value printed beside each displayed answer label. -/
def AnswerChoice.milliseconds : AnswerChoice → ℝ
  | .A => 180
  | .B => 160
  | .C => 140
  | .D => 120

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice is uniquely closest to the physical millisecond readout. -/
def IsClosestAnswerChoice
    (actualMilliseconds : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |actualMilliseconds - choice.milliseconds| <
      |actualMilliseconds - other.milliseconds|

/-!
Before answer-choice rounding, two `20 m` legs at `340 m/s` give the exact
idealized round-trip duration `2000/17 ms`.
-/
lemma roundTripTravelTime_milliseconds_eq
    (setup : AutofocusEchoSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_distance : HasStatedObjectDistance setup)
    (h_ultrasonic : EmitsUltrasonicPulse setup)
    (h_air : UsesStandardAirSoundSpeed setup)
    (h_physical : HasPhysicalEchoParameters setup)
    (h_propagation : SatisfiesEchoPropagationLaws setup) :
    durationInMilliseconds setup.roundTripTravelTime = (2000 : ℝ) / 17 := by
  have h_outbound_distance :
      lengthInMeters (setup.pathLength .outbound) = 20 := by
    rw [h_figure.outboundPathLength]
    exact h_distance
  have h_return_distance :
      lengthInMeters (setup.pathLength .reflectedReturn) = 20 := by
    rw [h_figure.reflectedReturnPathLength]
    exact h_distance
  have h_outbound :=
    h_propagation.constantSpeedPropagation PulseLeg.outbound
  have h_return :=
    h_propagation.constantSpeedPropagation PulseLeg.reflectedReturn
  change speedInMetersPerSecond setup.soundSpeedInAir = 340 at h_air
  rw [h_air, h_outbound_distance] at h_outbound
  rw [h_air, h_return_distance] at h_return
  have h_roundTrip_seconds :
      durationInSeconds setup.roundTripTravelTime = (2 : ℝ) / 17 := by
    nlinarith [h_propagation.roundTripTimeComposition]
  have h_seconds_to_milliseconds :
      durationInMilliseconds setup.roundTripTravelTime =
        1000 * durationInSeconds setup.roundTripTravelTime := by
    have h_units_val := congrArg WithDim.val <|
      setup.roundTripTravelTime.2
        UnitChoices.SI
        ({UnitChoices.SI with time := TimeUnit.milliseconds} : UnitChoices)
    have h_units_real :=
      congrArg (fun x : NNReal => (x : ℝ)) h_units_val
    norm_num [durationInMilliseconds, durationInSeconds, durationReadout,
        UnitChoices.dimScale, TimeUnit.milliseconds, TimeUnit.seconds,
        TimeUnit.scale, TimeUnit.div_eq_val, WithDim.smul_val,
        NNReal.smul_def] at h_units_real ⊢
    exact h_units_real
  rw [h_seconds_to_milliseconds, h_roundTrip_seconds]
  norm_num

/-!
The physical round-trip travel time is uniquely closest to recorded answer D,
`120 ms`, among the four displayed choices.

This formalizes `thm:physics:phyx_mini_0211:target`.
-/
theorem roundTripTravelTime_matches_recordedChoiceD
    (setup : AutofocusEchoSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_distance : HasStatedObjectDistance setup)
    (h_ultrasonic : EmitsUltrasonicPulse setup)
    (h_air : UsesStandardAirSoundSpeed setup)
    (h_physical : HasPhysicalEchoParameters setup)
    (h_propagation : SatisfiesEchoPropagationLaws setup) :
    IsClosestAnswerChoice
      (durationInMilliseconds setup.roundTripTravelTime)
      recordedDatasetAnswer := by
  unfold IsClosestAnswerChoice
  rw [roundTripTravelTime_milliseconds_eq setup h_figure h_distance
    h_ultrasonic h_air h_physical h_propagation]
  intro other h_other
  cases other
  · norm_num [recordedDatasetAnswer, AnswerChoice.milliseconds]
  · norm_num [recordedDatasetAnswer, AnswerChoice.milliseconds]
  · norm_num [recordedDatasetAnswer, AnswerChoice.milliseconds]
  · exact (h_other rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0211
