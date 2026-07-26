import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Beat frequency from two loudspeakers on a moving railroad car

Two identical loudspeakers are fixed at opposite ends of a railroad car moving
rightward through still air.  At the instant shown in the primary figure, the
stationary observer `B` is between the speakers.  Sound from the rear speaker
therefore travels rightward toward `B`, while sound from the front speaker
travels leftward toward `B`.  The two received frequencies have opposite
moving-source Doppler shifts and produce beats.

The bitmap, taken as primary evidence, places `B` on the stationary ground;
the auxiliary caption's statement that `B` stands on the car is inconsistent
with the image and with the problem text's stationary-observer description.

Frequencies, positions, sound speed, and signed axial velocities retain their
physical dimensions through Physlib.  Real numbers are used only for readouts
in named SI units and for the displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0222

open Dimension

/-! ## Dimensionful acoustic quantities and SI readouts -/

/-- A nonnegative physical acoustic frequency, with inverse-time dimension. -/
abbrev AcousticFrequency : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed physical coordinate on the horizontal axis of the figure. -/
abbrev AxialPosition : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/--
A signed physical velocity along the figure's horizontal axis.  Positive
velocity points to the right.
-/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical acoustic frequency in hertz. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read a signed axial position in metres. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  (position UnitChoices.SI).val

/-- Read a signed axial velocity in metres per second. -/
def axialVelocityInMetersPerSecond (velocity : AxialVelocity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Read Physlib's nonnegative physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-figure labels -/

/-- The three people labelled in the primary figure. -/
inductive FigurePerson where
  | A
  | B
  | C
  deriving DecidableEq, Repr

/-- The two loudspeakers attached to the railroad car. -/
inductive SpeakerLabel where
  | rear
  | front
  deriving DecidableEq, Repr

/-- The ends of the railroad car as oriented in the primary figure. -/
inductive RailroadCarEnd where
  | left
  | right
  deriving DecidableEq, Repr

/-- The carrier on which both sound sources are mounted. -/
inductive VehicleLabel where
  | railroadCar
  deriving DecidableEq, Repr

/-- The two orientations along the one-dimensional figure axis. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-!
Independent physical quantities for the two-source Doppler experiment.

The two received frequencies and `beatFrequencyAtB` are unknown physical
frequencies.  In particular, this setup does not assign the requested beat
frequency a numerical value.
-/
structure MovingRailroadCarSpeakerSetup where
  personPosition : FigurePerson → AxialPosition
  personVelocity : FigurePerson → AxialVelocity
  speakerPosition : SpeakerLabel → AxialPosition
  speakerVelocity : SpeakerLabel → AxialVelocity
  railroadCarVelocity : AxialVelocity
  airVelocity : AxialVelocity
  speakerCarrier : SpeakerLabel → VehicleLabel
  speakerEnd : SpeakerLabel → RailroadCarEnd
  emittedFrequency : SpeakerLabel → AcousticFrequency
  heardFrequencyAtB : SpeakerLabel → AcousticFrequency
  beatFrequencyAtB : AcousticFrequency
  soundSpeedInAir : DimSpeed
  propagationDirectionToB : SpeakerLabel → AxialDirection

/-- A speaker's signed velocity relative to the air, in metres per second. -/
def speakerVelocityRelativeToAirInMetersPerSecond
    (setup : MovingRailroadCarSpeakerSetup) (speaker : SpeakerLabel) : ℝ :=
  axialVelocityInMetersPerSecond (setup.speakerVelocity speaker) -
    axialVelocityInMetersPerSecond setup.airVelocity

/-- Observer `B`'s signed velocity relative to the air, in metres per second. -/
def observerBVelocityRelativeToAirInMetersPerSecond
    (setup : MovingRailroadCarSpeakerSetup) : ℝ :=
  axialVelocityInMetersPerSecond (setup.personVelocity .B) -
    axialVelocityInMetersPerSecond setup.airVelocity

/-!
Problem-statement and primary-figure data.

The picture orders `C`, the rear speaker, `B`, the front speaker, and `A` from
left to right.  Both speakers are fixed to the car, have the same `348 Hz`
emission, and move right with the car at `12 m/s`; observer `B` is stationary.
Consequently, sound reaching `B` from the rear and front speakers propagates
right and left respectively.

No heard frequency or beat-frequency value occurs in these data premises.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : MovingRailroadCarSpeakerSetup) : Prop where
  rearSpeakerOnCar : setup.speakerCarrier .rear = .railroadCar
  frontSpeakerOnCar : setup.speakerCarrier .front = .railroadCar
  rearSpeakerAtLeftEnd : setup.speakerEnd .rear = .left
  frontSpeakerAtRightEnd : setup.speakerEnd .front = .right
  figureLeftToRightOrder :
    positionInMeters (setup.personPosition .C) <
        positionInMeters (setup.speakerPosition .rear) ∧
      positionInMeters (setup.speakerPosition .rear) <
        positionInMeters (setup.personPosition .B) ∧
      positionInMeters (setup.personPosition .B) <
        positionInMeters (setup.speakerPosition .front) ∧
      positionInMeters (setup.speakerPosition .front) <
        positionInMeters (setup.personPosition .A)
  observerBStationary :
    axialVelocityInMetersPerSecond (setup.personVelocity .B) = 0
  railroadCarSpeedMetersPerSecond :
    axialVelocityInMetersPerSecond setup.railroadCarVelocity = 12
  speakersMoveWithCar : ∀ speaker,
    setup.speakerVelocity speaker = setup.railroadCarVelocity
  emittedFrequenciesIdentical :
    setup.emittedFrequency .rear = setup.emittedFrequency .front
  emittedFrequencyHertz :
    frequencyInHertz (setup.emittedFrequency .rear) = 348
  carMovesRight :
    0 < axialVelocityInMetersPerSecond setup.railroadCarVelocity
  rearSoundTravelsRight : setup.propagationDirectionToB .rear = .right
  frontSoundTravelsLeft : setup.propagationDirectionToB .front = .left

/-!
The source gives no numerical sound speed and does not explicitly state the
air motion.  This separate standard-ambient calibration supplies still air
and `343 m/s`, rather than presenting either as a figure readout or as part of
the requested conclusion.
-/
structure UsesStandardStillAir
    (setup : MovingRailroadCarSpeakerSetup) : Prop where
  airAtRest : axialVelocityInMetersPerSecond setup.airVelocity = 0
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeedInAir = 343

/-- Positivity and subsonic conditions for the classical acoustic model. -/
structure HasPhysicalDopplerParameters
    (setup : MovingRailroadCarSpeakerSetup) : Prop where
  emittedFrequenciesPositive : ∀ speaker,
    0 < frequencyInHertz (setup.emittedFrequency speaker)
  heardFrequenciesPositive : ∀ speaker,
    0 < frequencyInHertz (setup.heardFrequencyAtB speaker)
  soundSpeedPositive :
    0 < speedInMetersPerSecond setup.soundSpeedInAir
  speakersSubsonicRelativeToAir : ∀ speaker,
    |speakerVelocityRelativeToAirInMetersPerSecond setup speaker| <
      speedInMetersPerSecond setup.soundSpeedInAir

/-!
The one-dimensional classical Doppler laws for the two paths to stationary
observer `B`.  For the rear speaker the sound ray points right, giving

`f_rear = f₀ (c - u_B) / (c - u_rear)`.

For the front speaker the sound ray points left, so the signed velocity
projections reverse and

`f_front = f₀ (c + u_B) / (c + u_front)`.

All velocities are relative to the air.  These governing relations contain
neither the requested numerical beat frequency nor an answer label.
-/
structure SatisfiesDirectionalMovingSourceDopplerLaws
    (setup : MovingRailroadCarSpeakerSetup) : Prop where
  rearSpeakerFrequencyLaw :
    frequencyInHertz (setup.heardFrequencyAtB .rear) =
      frequencyInHertz (setup.emittedFrequency .rear) *
        (speedInMetersPerSecond setup.soundSpeedInAir -
          observerBVelocityRelativeToAirInMetersPerSecond setup) /
        (speedInMetersPerSecond setup.soundSpeedInAir -
          speakerVelocityRelativeToAirInMetersPerSecond setup .rear)
  frontSpeakerFrequencyLaw :
    frequencyInHertz (setup.heardFrequencyAtB .front) =
      frequencyInHertz (setup.emittedFrequency .front) *
        (speedInMetersPerSecond setup.soundSpeedInAir +
          observerBVelocityRelativeToAirInMetersPerSecond setup) /
        (speedInMetersPerSecond setup.soundSpeedInAir +
          speakerVelocityRelativeToAirInMetersPerSecond setup .front)

/-!
The acoustic definition of beat frequency: it is the magnitude of the
difference between the two frequencies received by `B`.  This law relates
three independent physical frequency quantities without fixing a numerical
answer.
-/
structure SatisfiesBeatFrequencyLaw
    (setup : MovingRailroadCarSpeakerSetup) : Prop where
  frequencyDifferenceLaw :
    frequencyInHertz setup.beatFrequencyAtB =
      |frequencyInHertz (setup.heardFrequencyAtB .rear) -
        frequencyInHertz (setup.heardFrequencyAtB .front)|

/-! ## Derived Doppler values and displayed answers -/

/--
The two directional Doppler laws give the exact received-frequency readouts
for the rear and front speakers under the explicit ambient calibration.
-/
lemma heardFrequenciesInHertz_eq_exactModelValues
    (setup : MovingRailroadCarSpeakerSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_ambient : UsesStandardStillAir setup)
    (_doppler : SatisfiesDirectionalMovingSourceDopplerLaws setup) :
    frequencyInHertz (setup.heardFrequencyAtB .rear) =
        (119364 : ℝ) / 331 ∧
      frequencyInHertz (setup.heardFrequencyAtB .front) =
        (119364 : ℝ) / 355 := by
  constructor
  · rw [_doppler.rearSpeakerFrequencyLaw,
        _problem.emittedFrequencyHertz,
        _ambient.soundSpeedMetersPerSecond]
    simp only [observerBVelocityRelativeToAirInMetersPerSecond,
      speakerVelocityRelativeToAirInMetersPerSecond,
      _problem.observerBStationary, _ambient.airAtRest,
      _problem.speakersMoveWithCar .rear,
      _problem.railroadCarSpeedMetersPerSecond]
    norm_num
  · have h_front :
        frequencyInHertz (setup.emittedFrequency .front) = 348 := by
      rw [← _problem.emittedFrequenciesIdentical]
      exact _problem.emittedFrequencyHertz
    rw [_doppler.frontSpeakerFrequencyLaw, h_front,
        _ambient.soundSpeedMetersPerSecond]
    simp only [observerBVelocityRelativeToAirInMetersPerSecond,
      speakerVelocityRelativeToAirInMetersPerSecond,
      _problem.observerBStationary, _ambient.airAtRest,
      _problem.speakersMoveWithCar .front,
      _problem.railroadCarSpeedMetersPerSecond]
    norm_num

/--
Combining the two received frequencies with the beat-frequency law gives the
exact classical-model beat readout, about `24.38 Hz`.
-/
lemma beatFrequencyInHertz_eq_exactModelValue
    (setup : MovingRailroadCarSpeakerSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_ambient : UsesStandardStillAir setup)
    (_doppler : SatisfiesDirectionalMovingSourceDopplerLaws setup)
    (_beatLaw : SatisfiesBeatFrequencyLaw setup) :
    frequencyInHertz setup.beatFrequencyAtB =
      (2864736 : ℝ) / 117505 := by
  rw [_beatLaw.frequencyDifferenceLaw]
  obtain ⟨h_rear, h_front⟩ :=
    heardFrequenciesInHertz_eq_exactModelValues setup _problem _ambient _doppler
  rw [h_rear, h_front]
  norm_num [abs_of_nonneg]

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Whole-hertz beat frequency printed beside each displayed answer label. -/
def AnswerChoice.hertz : AnswerChoice → ℝ
  | .A => 30
  | .B => 18
  | .C => 12
  | .D => 24

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
A physical beat frequency agrees with a displayed whole-hertz choice when its
SI readout rounds to that integer.  The tolerance is half a hertz.
-/
def MatchesAnswerChoice
    (frequency : AcousticFrequency) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ 1 / 2

/-!
The exact classical Doppler model gives approximately `24.38 Hz`, which rounds
to the displayed `24 Hz` value and hence matches recorded answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0222:target`.
-/
theorem beatFrequencyAtB_matches_recordedAnswerD
    (setup : MovingRailroadCarSpeakerSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_ambient : UsesStandardStillAir setup)
    (_physical : HasPhysicalDopplerParameters setup)
    (_doppler : SatisfiesDirectionalMovingSourceDopplerLaws setup)
    (_beatLaw : SatisfiesBeatFrequencyLaw setup) :
    frequencyInHertz setup.beatFrequencyAtB =
        (2864736 : ℝ) / 117505 ∧
      MatchesAnswerChoice setup.beatFrequencyAtB recordedAnswerChoice := by
  have h_exact :=
    beatFrequencyInHertz_eq_exactModelValue setup _problem _ambient _doppler _beatLaw
  refine ⟨h_exact, ?_⟩
  simp only [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.hertz, h_exact]
  norm_num [abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0222
