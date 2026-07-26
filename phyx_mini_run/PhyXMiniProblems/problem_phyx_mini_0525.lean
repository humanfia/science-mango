import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0525

open Dimension

/-!
# Beat frequency measured by police microwave radar

A roadside radar broadcasts a microwave carrier toward an approaching car.
The car reflects a Doppler-shifted signal, which the receiver mixes with an
attenuated copy of the transmitted carrier. The measured beat frequency is
the absolute frequency difference of those two receiver inputs.

Frequency and speed magnitudes below are unit-independent Physlib quantities.
Real numbers occur only as named-unit readouts, dimensionless relative
amplitudes, and displayed numerical answers. In particular, the measured beat
frequency is an independent physical quantity: it is related to the signals
only by the Doppler and mixer laws stated below.
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

/-- Gigahertz readout of a physical frequency. -/
def frequencyInGigahertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyInHertz frequency / 1000000000

/-- Kilohertz readout of a physical frequency. -/
def frequencyInKilohertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyInHertz frequency / 1000

/-- Meters-per-second readout of a physical speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Direction in which a microwave signal travels in the radar experiment. -/
inductive MicrowaveTravelDirection where
  | radarToCar
  | carToRadar
  | internalReference
  deriving DecidableEq, Repr

/-- Whether the car's radial motion is toward or away from the radar. -/
inductive RadialMotion where
  | approaching
  | receding
  deriving DecidableEq, Repr

/-- Sign of the reflected Doppler shift in the chosen radial convention. -/
def radialDopplerSign : RadialMotion → ℝ
  | .approaching => 1
  | .receding => -1

/-!
A microwave signal has a dimensionful frequency and a nonnegative relative
amplitude. The latter is a dimensionless receiver-level readout, used only to
express that the local reference has been attenuated.
-/
structure MicrowaveSignal where
  frequency : FrequencyQuantity
  relativeAmplitude : NNReal
  travelDirection : MicrowaveTravelDirection

/-!
Qualitative information visible in the supplied primary image. The two
numerals are display contents, not calibrated SI speed data. The bitmap does
not show a microwave beam or a line-of-sight angle.
-/
structure RoadsideRadarFigure where
  speedLimitLabel : String
  speedLimitNumeral : ℕ
  measuredSpeedLabel : String
  measuredSpeedNumeral : ℕ
  isMountedOnTrailer : Bool
  showsMicrowavePathGeometry : Bool

/-!
The three signals, the car and propagation speeds, and the beat-frequency
output of one police-radar measurement. None of these fields is defined in
terms of the requested numerical answer.
-/
structure PoliceRadarBeatSetup where
  transmittedMicrowave : MicrowaveSignal
  reflectedMicrowave : MicrowaveSignal
  attenuatedReference : MicrowaveSignal
  measuredBeatFrequency : FrequencyQuantity
  carSpeed : SpeedQuantity
  microwavePropagationSpeed : SpeedQuantity
  carRadialMotion : RadialMotion
  figure : RoadsideRadarFigure

/-- The signal paths have the physical roles described in the problem. -/
structure HasRadarSignalRouting (setup : PoliceRadarBeatSetup) : Prop where
  transmittedTowardCar :
    setup.transmittedMicrowave.travelDirection = .radarToCar
  reflectionReturnsToRadar :
    setup.reflectedMicrowave.travelDirection = .carToRadar
  referenceRemainsInsideReceiver :
    setup.attenuatedReference.travelDirection = .internalReference

/-- Facts read directly from the supplied roadside-radar image. -/
structure MatchesPrimaryFigure (setup : PoliceRadarBeatSetup) : Prop where
  speedLimitLabel : setup.figure.speedLimitLabel = "SPEED LIMIT"
  speedLimitNumeral : setup.figure.speedLimitNumeral = 25
  measuredSpeedLabel : setup.figure.measuredSpeedLabel = "YOUR SPEED"
  measuredSpeedNumeral : setup.figure.measuredSpeedNumeral = 22
  mountedOnTrailer : setup.figure.isMountedOnTrailer = true
  noMicrowaveGeometryShown :
    setup.figure.showsMicrowavePathGeometry = false

/-!
Numerical readouts and motion sense stated for the calculation. The carrier is
`10.0 GHz`, the car's radial speed magnitude is `30.0 m/s`, and vacuum
microwaves propagate at Physlib's exact SI speed of light. Its SI readout is
`299792458 m/s` by `DimSpeed.speedOfLight_in_SI`. These fields contain no
beat-frequency value.
-/
structure MatchesProblemReadouts (setup : PoliceRadarBeatSetup) : Prop where
  transmittedFrequencyGigahertz :
    frequencyInGigahertz setup.transmittedMicrowave.frequency = 10
  carSpeedMetersPerSecond : speedInMetersPerSecond setup.carSpeed = 30
  microwaveSpeedMetersPerSecond :
    speedInMetersPerSecond setup.microwavePropagationSpeed =
      (DimSpeed.speedOfLight UnitChoices.SI).val
  carIsApproaching : setup.carRadialMotion = .approaching

/-!
Physical-domain conditions for the ideal longitudinal radar model. In
particular, the car is slower than the microwave propagation speed, so the
factor `c - v` in the approaching-reflector relation is positive.
-/
structure HasPhysicalRadarParameters (setup : PoliceRadarBeatSetup) : Prop where
  transmittedFrequencyPositive :
    0 < frequencyInHertz setup.transmittedMicrowave.frequency
  reflectedFrequencyPositive :
    0 < frequencyInHertz setup.reflectedMicrowave.frequency
  propagationSpeedPositive :
    0 < speedInMetersPerSecond setup.microwavePropagationSpeed
  carSpeedBelowPropagationSpeed :
    speedInMetersPerSecond setup.carSpeed <
      speedInMetersPerSecond setup.microwavePropagationSpeed

/-!
Attenuation changes the local reference amplitude but preserves its carrier
frequency. This governing receiver relation does not determine the beat output
by itself.
-/
structure SatisfiesAttenuatedReferenceLaw
    (setup : PoliceRadarBeatSetup) : Prop where
  carrierFrequencyPreserved :
    frequencyInHertz setup.attenuatedReference.frequency =
      frequencyInHertz setup.transmittedMicrowave.frequency
  referenceAmplitudeReduced :
    setup.attenuatedReference.relativeAmplitude <
      setup.transmittedMicrowave.relativeAmplitude

/-!
The exact ideal longitudinal moving-reflector relation

`(c - s * v) * f_reflected = (c + s * v) * f_transmitted`,

where `s` is positive for an approaching car and negative for a receding car.
For an approaching reflector this is `(c-v) f_reflected =
(c+v) f_transmitted`. It incorporates the outgoing and return Doppler shifts
without asserting the low-speed approximation `Δf = 2 f v / c` as a global
equality. This governing law does not mention the requested answer.
-/
structure SatisfiesExactLongitudinalMovingReflectorLaw
    (setup : PoliceRadarBeatSetup) : Prop where
  reflectedFrequencyRelation :
    (speedInMetersPerSecond setup.microwavePropagationSpeed -
          radialDopplerSign setup.carRadialMotion *
            speedInMetersPerSecond setup.carSpeed) *
        frequencyInHertz setup.reflectedMicrowave.frequency =
      (speedInMetersPerSecond setup.microwavePropagationSpeed +
          radialDopplerSign setup.carRadialMotion *
            speedInMetersPerSecond setup.carSpeed) *
        frequencyInHertz setup.transmittedMicrowave.frequency

/-!
Mixing the received reflection with the attenuated carrier copy produces a beat
at the absolute difference of their frequencies.
-/
structure SatisfiesBeatMixerLaw (setup : PoliceRadarBeatSetup) : Prop where
  beatIsAbsoluteFrequencyDifference :
    frequencyInHertz setup.measuredBeatFrequency =
      |frequencyInHertz setup.reflectedMicrowave.frequency -
        frequencyInHertz setup.attenuatedReference.frequency|

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-!
Numerical kilohertz value printed beside each answer label. The source's answer
strings are truncated after the number; kilohertz is the dimensionally
consistent scale for the listed values and the radar calculation.
-/
def displayedAnswerBeatFrequencyInKilohertz : AnswerChoice → ℝ
  | .A => 14 / 5
  | .B => 9 / 5
  | .C => 3 / 2
  | .D => 2

/-!
A frequency rounds to the displayed hundredth of a kilohertz when its readout
is strictly within `0.005 kHz` of the displayed value.
-/
def RoundsToNearestHundredthKilohertz
    (frequency : FrequencyQuantity) (displayedValue : ℝ) : Prop :=
  |frequencyInKilohertz frequency - displayedValue| < (1 / 200 : ℝ)

/-- The measured beat frequency agrees with a displayed answer choice. -/
def MatchesAnswerChoice
    (setup : PoliceRadarBeatSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredthKilohertz setup.measuredBeatFrequency
    (displayedAnswerBeatFrequencyInKilohertz choice)

/-!
Substitution of the stated readouts into the exact moving-reflector,
attenuation, and mixer laws bounds the ideal beat-frequency readout strictly
between `2.000 kHz` and `2.005 kHz`.
-/
lemma measuredBeatFrequency_exact_readout
    (setup : PoliceRadarBeatSetup)
    (hProblem : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalRadarParameters setup)
    (hReference : SatisfiesAttenuatedReferenceLaw setup)
    (hDoppler : SatisfiesExactLongitudinalMovingReflectorLaw setup)
    (hMixer : SatisfiesBeatMixerLaw setup) :
    (2 : ℝ) < frequencyInKilohertz setup.measuredBeatFrequency ∧
      frequencyInKilohertz setup.measuredBeatFrequency < (401 / 200 : ℝ) := by
  have hTransmitted :
      frequencyInHertz setup.transmittedMicrowave.frequency = 10000000000 := by
    have h := hProblem.transmittedFrequencyGigahertz
    norm_num [frequencyInGigahertz] at h ⊢
    linarith
  have hCarSpeed : speedInMetersPerSecond setup.carSpeed = 30 :=
    hProblem.carSpeedMetersPerSecond
  have hMicrowaveSpeed :
      speedInMetersPerSecond setup.microwavePropagationSpeed = 299792458 := by
    rw [hProblem.microwaveSpeedMetersPerSecond]
    norm_num
  have hDoppler' := hDoppler.reflectedFrequencyRelation
  rw [hProblem.carIsApproaching] at hDoppler'
  simp only [radialDopplerSign, one_mul] at hDoppler'
  rw [hMicrowaveSpeed, hCarSpeed, hTransmitted] at hDoppler'
  norm_num at hDoppler'
  have hReflectedGreater :
      frequencyInHertz setup.transmittedMicrowave.frequency <
        frequencyInHertz setup.reflectedMicrowave.frequency := by
    rw [hTransmitted]
    nlinarith [hDoppler']
  have hBeat := hMixer.beatIsAbsoluteFrequencyDifference
  rw [hReference.carrierFrequencyPreserved, abs_of_pos] at hBeat
  · constructor <;>
      simp only [frequencyInKilohertz]
    · rw [hBeat, hTransmitted]
      nlinarith [hDoppler']
    · rw [hBeat, hTransmitted]
      norm_num
      nlinarith [hDoppler']
  · exact sub_pos.mpr hReflectedGreater

/-!
Under the exact ideal-model laws, the beat readout lies between `2.000 kHz`
and `2.005 kHz`, so it rounds to the displayed `2.00 kHz` and matches answer
choice D.

This formalizes `thm:physics:phyx_mini_0525:target`.
-/
theorem problem_phyx_mini_0525
    (setup : PoliceRadarBeatSetup)
    (hRouting : HasRadarSignalRouting setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalRadarParameters setup)
    (hReference : SatisfiesAttenuatedReferenceLaw setup)
    (hDoppler : SatisfiesExactLongitudinalMovingReflectorLaw setup)
    (hMixer : SatisfiesBeatMixerLaw setup) :
    ((2 : ℝ) < frequencyInKilohertz setup.measuredBeatFrequency ∧
        frequencyInKilohertz setup.measuredBeatFrequency < (401 / 200 : ℝ)) ∧
      RoundsToNearestHundredthKilohertz
        setup.measuredBeatFrequency 2 ∧
      MatchesAnswerChoice setup .D := by
  have hBounds := measuredBeatFrequency_exact_readout setup hProblem hPhysical
    hReference hDoppler hMixer
  have hRounds :
      RoundsToNearestHundredthKilohertz setup.measuredBeatFrequency 2 := by
    rw [RoundsToNearestHundredthKilohertz, abs_lt]
    constructor
    · norm_num
      linarith [hBounds.1]
    · norm_num
      linarith [hBounds.2]
  exact ⟨hBounds, hRounds, by simpa [MatchesAnswerChoice,
    displayedAnswerBeatFrequencyInKilohertz] using hRounds⟩

end PhyXMiniProblems.ProblemPhyXMini0525
