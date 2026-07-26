import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0319

open Dimension

/-!
# Sonar reflected between two approaching submarines

The French submarine is on the left and moves right at `50 km/h`; the U.S.
submarine is on the right and moves left at `70 km/h`.  In motionless water,
the French submarine emits a `1000 Hz` sonar wave to the right.  The U.S.
submarine reflects it, and the French submarine detects the leftward return.

There are two classical acoustic Doppler shifts.  On the outbound leg the
French submarine is the moving source and the U.S. submarine is the moving
observer.  Ideal reflection preserves frequency in the U.S. submarine's rest
frame.  On the return leg the U.S. submarine acts as the moving source and the
French submarine as the moving observer.

Frequency and speed magnitudes are unit-independent Physlib quantities.  Real
scalars below are used only for named-unit readouts, signed horizontal
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

/-- Kilometers-per-hour readout of a physical speed magnitude. -/
def speedInKilometersPerHour (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.kilometers TimeUnit.hours speed

/-! ## Submarines, directions, and primary-figure data -/

/-- The two physical bodies in the sonar experiment. -/
inductive Submarine where
  | french
  | unitedStates
  deriving DecidableEq, Repr

/-- The geographic setting named in the problem statement. -/
inductive ManeuverRegion where
  | northAtlantic
  deriving DecidableEq, Repr

/-- The two submarine labels printed in the supplied bitmap. -/
inductive FigureLabel where
  | french
  | unitedStates
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

/-!
Signed velocity readout, positive toward the right of the figure, in selected
length and time units.
-/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (motion : HorizontalMotion) : ℝ :=
  match motion.direction with
  | .left => -speedReadout lengthUnit timeUnit motion.speedMagnitude
  | .right => speedReadout lengthUnit timeUnit motion.speedMagnitude

/-- Signed velocity in kilometers per hour, positive to the image's right. -/
def signedVelocityInKilometersPerHour (motion : HorizontalMotion) : ℝ :=
  signedVelocityReadout LengthUnit.kilometers TimeUnit.hours motion

/-- Propagation sign along the same right-positive horizontal axis. -/
def propagationSign : HorizontalDirection → ℝ
  | .left => -1
  | .right => 1

/-!
Qualitative information read directly from the primary bitmap.  Pixel
coordinates preserve only horizontal ordering, not physical distance.  The
upper black arrow is the reflected leftward wave and the lower arrow is the
outbound rightward wave.
-/
structure SubmarineSonarFigure where
  labelPositionFromLeftPixels : FigureLabel → ℝ
  frenchVelocityArrowDirection : HorizontalDirection
  unitedStatesVelocityArrowDirection : HorizontalDirection
  outboundWaveArrowDirection : HorizontalDirection
  reflectedWaveArrowDirection : HorizontalDirection
  showsFrenchVelocityLabel : Bool
  showsUnitedStatesVelocityLabel : Bool
  showsBrokenWavefrontsBetweenSubmarines : Bool

/-!
Independent physical quantities for the emitted, incident, reflected, and
detected sonar waves.  In particular, the detected frequency is not defined
from a Doppler formula or from an answer choice; the governing laws below
relate it to the other quantities.
-/
structure SubmarineSonarReflectionSetup where
  motion : Submarine → HorizontalMotion
  waterMotion : HorizontalMotion
  physicalPositionFromLeftKilometers : Submarine → ℝ
  maneuverRegion : ManeuverRegion
  sonarSpeedInWater : SpeedQuantity
  emittedFrequency : FrequencyQuantity
  incidentFrequencyInUnitedStatesFrame : FrequencyQuantity
  reflectedFrequencyInUnitedStatesFrame : FrequencyQuantity
  detectedReflectedFrequency : FrequencyQuantity
  outboundPropagationDirection : HorizontalDirection
  returnPropagationDirection : HorizontalDirection
  signalIsSonarSoundWave : Bool
  unitedStatesSubmarineActsAsReflector : Bool
  figure : SubmarineSonarFigure

/-!
Primary-image evidence: the French submarine is left of the U.S. submarine;
its `v_F` arrow points right, the `v_US` arrow points left, the outbound and
return arrows point right and left respectively, and broken wavefronts are
drawn between the submarines.
-/
structure MatchesPrimaryFigure
    (setup : SubmarineSonarReflectionSetup) : Prop where
  frenchLeftOfUnitedStatesInImage :
    setup.figure.labelPositionFromLeftPixels .french <
      setup.figure.labelPositionFromLeftPixels .unitedStates
  frenchVelocityArrowPointsRight :
    setup.figure.frenchVelocityArrowDirection = .right
  unitedStatesVelocityArrowPointsLeft :
    setup.figure.unitedStatesVelocityArrowDirection = .left
  outboundWaveArrowPointsRight :
    setup.figure.outboundWaveArrowDirection = .right
  reflectedWaveArrowPointsLeft :
    setup.figure.reflectedWaveArrowDirection = .left
  frenchVelocityLabelShown :
    setup.figure.showsFrenchVelocityLabel = true
  unitedStatesVelocityLabelShown :
    setup.figure.showsUnitedStatesVelocityLabel = true
  brokenWavefrontsShown :
    setup.figure.showsBrokenWavefrontsBetweenSubmarines = true

/-!
Problem-statement data: the two submarines approach one another at `50 km/h`
and `70 km/h`, the emitted sonar frequency is `1000 Hz`, the wave speed is
`5470 km/h`, and the North Atlantic water is motionless.  No value of the
requested detected frequency occurs here.
-/
structure MatchesProblemReadouts
    (setup : SubmarineSonarReflectionSetup) : Prop where
  regionIsNorthAtlantic :
    setup.maneuverRegion = .northAtlantic
  emittedFrequencyHertz :
    frequencyInHertz setup.emittedFrequency = 1000
  frenchSpeedKilometersPerHour :
    speedInKilometersPerHour (setup.motion .french).speedMagnitude = 50
  frenchMovesRight :
    (setup.motion .french).direction = .right
  unitedStatesSpeedKilometersPerHour :
    speedInKilometersPerHour
        (setup.motion .unitedStates).speedMagnitude = 70
  unitedStatesMovesLeft :
    (setup.motion .unitedStates).direction = .left
  sonarSpeedKilometersPerHour :
    speedInKilometersPerHour setup.sonarSpeedInWater = 5470
  waterIsMotionless :
    speedInKilometersPerHour setup.waterMotion.speedMagnitude = 0
  frenchSubmarineLeftOfUnitedStatesSubmarine :
    setup.physicalPositionFromLeftKilometers .french <
      setup.physicalPositionFromLeftKilometers .unitedStates
  outboundSonarMovesRight :
    setup.outboundPropagationDirection = .right
  reflectedSonarMovesLeft :
    setup.returnPropagationDirection = .left
  signalIsSonar : setup.signalIsSonarSoundWave = true
  unitedStatesSubmarineReflectsSignal :
    setup.unitedStatesSubmarineActsAsReflector = true

/-!
Positivity and subsonic conditions under which both classical acoustic
Doppler relations are physically meaningful.
-/
structure HasPhysicalAcousticParameters
    (setup : SubmarineSonarReflectionSetup) : Prop where
  emittedFrequencyPositive :
    0 < frequencyInHertz setup.emittedFrequency
  incidentFrequencyPositive :
    0 < frequencyInHertz setup.incidentFrequencyInUnitedStatesFrame
  reflectedFrequencyPositive :
    0 < frequencyInHertz setup.reflectedFrequencyInUnitedStatesFrame
  detectedFrequencyPositive :
    0 < frequencyInHertz setup.detectedReflectedFrequency
  sonarSpeedPositive :
    0 < speedInKilometersPerHour setup.sonarSpeedInWater
  frenchSubmarineSubsonicRelativeToWater :
    |signedVelocityInKilometersPerHour (setup.motion .french) -
        signedVelocityInKilometersPerHour setup.waterMotion| <
      speedInKilometersPerHour setup.sonarSpeedInWater
  unitedStatesSubmarineSubsonicRelativeToWater :
    |signedVelocityInKilometersPerHour (setup.motion .unitedStates) -
        signedVelocityInKilometersPerHour setup.waterMotion| <
      speedInKilometersPerHour setup.sonarSpeedInWater

/-! ## Governing acoustic laws -/

/-!
The classical one-dimensional acoustic Doppler relation on both signal legs.
For propagation sign `q`, source velocity `v_s`, observer velocity `v_o`,
water velocity `v_m`, and sonar speed `c` relative to the water, the
multiplicative factor is

`(c - q * (v_o - v_m)) / (c - q * (v_s - v_m))`.

On the outbound leg the French submarine emits and the U.S. submarine
observes.  On the return leg the U.S. submarine emits the reflected signal in
its rest frame and the French submarine observes.  These laws hold in every
compatible choice of length and time units and contain no requested answer
value.
-/
structure SatisfiesTwoLegAcousticDopplerLaw
    (setup : SubmarineSonarReflectionSetup) : Prop where
  outboundLeg :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      frequencyReadout timeUnit
          setup.incidentFrequencyInUnitedStatesFrame =
        frequencyReadout timeUnit setup.emittedFrequency *
          (speedReadout lengthUnit timeUnit setup.sonarSpeedInWater -
            propagationSign setup.outboundPropagationDirection *
              (signedVelocityReadout lengthUnit timeUnit
                  (setup.motion .unitedStates) -
                signedVelocityReadout lengthUnit timeUnit
                  setup.waterMotion)) /
          (speedReadout lengthUnit timeUnit setup.sonarSpeedInWater -
            propagationSign setup.outboundPropagationDirection *
              (signedVelocityReadout lengthUnit timeUnit
                  (setup.motion .french) -
                signedVelocityReadout lengthUnit timeUnit
                  setup.waterMotion))
  returnLeg :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      frequencyReadout timeUnit setup.detectedReflectedFrequency =
        frequencyReadout timeUnit
            setup.reflectedFrequencyInUnitedStatesFrame *
          (speedReadout lengthUnit timeUnit setup.sonarSpeedInWater -
            propagationSign setup.returnPropagationDirection *
              (signedVelocityReadout lengthUnit timeUnit
                  (setup.motion .french) -
                signedVelocityReadout lengthUnit timeUnit
                  setup.waterMotion)) /
          (speedReadout lengthUnit timeUnit setup.sonarSpeedInWater -
            propagationSign setup.returnPropagationDirection *
              (signedVelocityReadout lengthUnit timeUnit
                  (setup.motion .unitedStates) -
                signedVelocityReadout lengthUnit timeUnit
                  setup.waterMotion))

/-!
Ideal reflection preserves the incident frequency in the U.S. submarine's
rest frame.  This boundary law relates two independent physical frequency
quantities; it does not state the frequency later received by the French
submarine.
-/
structure SatisfiesIdealReflectionInUnitedStatesFrame
    (setup : SubmarineSonarReflectionSetup) : Prop where
  reflectedEqualsIncidentInUnitedStatesFrame :
    ∀ timeUnit : TimeUnit,
      frequencyReadout timeUnit
          setup.reflectedFrequencyInUnitedStatesFrame =
        frequencyReadout timeUnit
          setup.incidentFrequencyInUnitedStatesFrame

/-! ## Displayed answers and formalization target -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each answer label. -/
def displayedAnswerFrequencyInHertz : AnswerChoice → ℝ
  | .A => 1005
  | .B => 1021
  | .C => 1032
  | .D => 1045

/-- The answer label recorded in the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A physical frequency readout rounds to the displayed whole-hertz value when
it lies strictly within half a hertz of that value.
-/
def RoundsToNearestHertz
    (frequency : FrequencyQuantity) (nearestWholeHertz : ℝ) : Prop :=
  |frequencyInHertz frequency - nearestWholeHertz| < (1 / 2 : ℝ)

/-- The modeled reflected signal agrees with a displayed answer choice. -/
def MatchesAnswerChoice
    (setup : SubmarineSonarReflectionSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHertz setup.detectedReflectedFrequency
    (displayedAnswerFrequencyInHertz choice)

/-!
The two Doppler shifts and the rest-frame reflection law give the unrounded
double-shifted readout

`1000 * (5470 + 70) / (5470 - 50) * (5470 + 50) / (5470 - 70)` hertz.
-/
lemma detectedReflectedFrequency_doppler_readout
    (setup : SubmarineSonarReflectionSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hDoppler : SatisfiesTwoLegAcousticDopplerLaw setup)
    (hReflection : SatisfiesIdealReflectionInUnitedStatesFrame setup) :
    frequencyInHertz setup.detectedReflectedFrequency =
      1000 * (5470 + 70) / (5470 - 50) *
        (5470 + 50) / (5470 - 70) := by
  have hSpeedConversion (speed : SpeedQuantity) :
      speedReadout LengthUnit.meters TimeUnit.seconds speed =
        (5 / 18 : ℝ) * speedInKilometersPerHour speed := by
    let kilometersPerHour : UnitChoices :=
      {UnitChoices.SI with
        length := LengthUnit.kilometers, time := TimeUnit.hours}
    have hSpeedScale :
        kilometersPerHour.dimScale UnitChoices.SI (L𝓭 * T𝓭⁻¹) =
          (⟨5 / 18, by norm_num⟩ : NNReal) := by
      simp [kilometersPerHour, UnitChoices.dimScale,
        LengthUnit.kilometers, TimeUnit.hours]
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_rpow]
      norm_num [NNReal.toReal]
    have hUnits :=
      congrArg (fun quantity : WithDim (L𝓭 * T𝓭⁻¹) NNReal =>
        (quantity.val : ℝ))
        (speed.2 kilometersPerHour UnitChoices.SI)
    rw [show dim (WithDim (L𝓭 * T𝓭⁻¹) NNReal) = L𝓭 * T𝓭⁻¹ by rfl,
      hSpeedScale] at hUnits
    dsimp [kilometersPerHour, speedReadout,
      speedInKilometersPerHour] at hUnits
    norm_num at hUnits
    exact hUnits
  have hEmitted :
      frequencyReadout TimeUnit.seconds setup.emittedFrequency = 1000 :=
    hProblem.emittedFrequencyHertz
  have hFrenchSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .french).speedMagnitude =
        (5 / 18 : ℝ) * 50 := by
    rw [hSpeedConversion, hProblem.frenchSpeedKilometersPerHour]
  have hUnitedStatesSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .unitedStates).speedMagnitude =
        (5 / 18 : ℝ) * 70 := by
    rw [hSpeedConversion, hProblem.unitedStatesSpeedKilometersPerHour]
  have hSonarSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.sonarSpeedInWater =
        (5 / 18 : ℝ) * 5470 := by
    rw [hSpeedConversion, hProblem.sonarSpeedKilometersPerHour]
  have hWaterSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.waterMotion.speedMagnitude = 0 := by
    rw [hSpeedConversion, hProblem.waterIsMotionless]
    norm_num
  have hFrenchVelocity :
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .french) =
        (5 / 18 : ℝ) * 50 := by
    simp [signedVelocityReadout, hProblem.frenchMovesRight, hFrenchSpeed]
  have hUnitedStatesVelocity :
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
          (setup.motion .unitedStates) =
        -((5 / 18 : ℝ) * 70) := by
    simp [signedVelocityReadout, hProblem.unitedStatesMovesLeft,
      hUnitedStatesSpeed]
  have hWaterVelocity :
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
          setup.waterMotion = 0 := by
    cases hDirection : setup.waterMotion.direction <;>
      simp [signedVelocityReadout, hDirection, hWaterSpeed]
  have hOutbound :=
    hDoppler.outboundLeg LengthUnit.meters TimeUnit.seconds
  have hReturn :=
    hDoppler.returnLeg LengthUnit.meters TimeUnit.seconds
  have hReflect :=
    hReflection.reflectedEqualsIncidentInUnitedStatesFrame TimeUnit.seconds
  simp [hProblem.outboundSonarMovesRight, propagationSign,
    hEmitted, hSonarSpeed, hFrenchVelocity, hUnitedStatesVelocity,
    hWaterVelocity] at hOutbound
  simp [hProblem.reflectedSonarMovesLeft, propagationSign,
    hSonarSpeed, hFrenchVelocity, hUnitedStatesVelocity,
    hWaterVelocity] at hReturn
  rw [hReflect, hOutbound] at hReturn
  change frequencyReadout TimeUnit.seconds
      setup.detectedReflectedFrequency =
    1000 * (5470 + 70) / (5470 - 50) *
      (5470 + 50) / (5470 - 70)
  norm_num at hReturn ⊢
  exact hReturn

/-!
The exact ideal-model readout is `2548400 / 2439` hertz, approximately
`1044.85 Hz`, and therefore rounds to `1045 Hz`, answer choice D.

This formalizes `thm:physics:phyx_mini_0319:target`.
-/
theorem problem_phyx_mini_0319
    (setup : SubmarineSonarReflectionSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hDoppler : SatisfiesTwoLegAcousticDopplerLaw setup)
    (hReflection : SatisfiesIdealReflectionInUnitedStatesFrame setup) :
    frequencyInHertz setup.detectedReflectedFrequency = 2548400 / 2439 ∧
      RoundsToNearestHertz setup.detectedReflectedFrequency 1045 ∧
      MatchesAnswerChoice setup .D := by
  have hDetected :=
    detectedReflectedFrequency_doppler_readout setup hFigure hProblem
      hPhysical hDoppler hReflection
  constructor
  · calc
      frequencyInHertz setup.detectedReflectedFrequency =
          1000 * (5470 + 70) / (5470 - 50) *
            (5470 + 50) / (5470 - 70) := hDetected
      _ = 2548400 / 2439 := by norm_num
  constructor
  · rw [RoundsToNearestHertz, hDetected]
    norm_num [abs_of_nonneg, abs_of_neg]
  · rw [MatchesAnswerChoice, displayedAnswerFrequencyInHertz,
      RoundsToNearestHertz, hDetected]
    norm_num [abs_of_nonneg, abs_of_neg]

end PhyXMiniProblems.ProblemPhyXMini0319
