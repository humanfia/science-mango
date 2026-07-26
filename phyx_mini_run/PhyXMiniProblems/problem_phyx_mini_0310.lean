import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Pulse frequency from regularly spaced amphitheater terraces

A handclap is emitted from a stage toward a stepped terrace.  Successive
vertical reflecting faces are separated horizontally by the labeled terrace
width `w = 0.75 m`.  Under the problem's horizontal-ray idealization, a pulse
reflected from the next face travels an additional distance `w` on its outbound
leg and an additional distance `w` on its return leg.  The adjacent echo path
difference is therefore `2w`.

Lengths, positions, durations, frequencies, and sound speed are represented by
unit-independent Physlib quantities.  Real numbers below occur only as
readouts in explicitly selected units or as displayed answer values.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the staged source, the stepped
  terrace, the labels `w` and `Terrace`, the width `0.75 m`, one reflected pulse
  per riser, the horizontal-ray assumption, and the spacing of adjacent risers;
* `UsesStandardAirSoundSpeed` supplies the separate textbook air-speed
  calibration `343 m/s`, which is not printed in the source question;
* `SatisfiesTerraceEchoLaws` states horizontal out-and-back path geometry,
  constant-speed propagation, composition of the two leg times, periodicity of
  adjacent returns, and the period--frequency law;
* the values `3/686 s`, `686/3 Hz`, and the selected answer D occur only in
  conclusions or in the displayed-answer table, never in a physical premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0310

open Dimension

/-! ## Dimensionful acoustic quantities and named-unit readouts -/

/-- A nonnegative physical path length or terrace width. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial position along the horizontal stage-to-terrace direction. -/
abbrev AxialPosition : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical propagation duration. -/
abbrev AcousticDuration : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical pulse-return frequency. -/
abbrev AcousticFrequency : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Physlib's nonnegative dimensionful speed type. -/
abbrev AcousticSpeed : Type := DimSpeed

/-- Read a nonnegative length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed axial position in a selected length unit. -/
def positionReadout (unit : LengthUnit) (position : AxialPosition) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a physical duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : AcousticDuration) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of a selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in selected coherent length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : AcousticSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a physical path length or terrace width. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Meter readout of a signed horizontal position. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  positionReadout LengthUnit.meters position

/-- Second readout of an acoustic duration. -/
def durationInSeconds (duration : AcousticDuration) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Hertz readout of a pulse-return frequency. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of the propagation speed. -/
def speedInMetersPerSecond (speed : AcousticSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical roles and primary-image labels -/

/-- Named physical objects appearing in the problem and its primary image. -/
inductive FigureObject where
  | handclapper
  | stagePlatform
  | steppedTerrace
  | reflectingRiser
  deriving DecidableEq, Repr

/-- Textual and symbolic labels visible in the primary image. -/
inductive FigureLabel where
  | width_w
  | terrace
  deriving DecidableEq, Repr

/-- The two legs of an echo path from the stage to a riser and back. -/
inductive EchoLeg where
  | outbound
  | reflectedReturn
  deriving DecidableEq, Repr

/-- Axial directions for the outbound and returning sound rays. -/
inductive AxialDirection where
  | stageToTerrace
  | terraceToStage
  deriving DecidableEq, Repr

/-- Orientations admitted by the diagram before imposing the question's idealization. -/
inductive RayOrientation where
  | horizontal
  | nonhorizontal
  deriving DecidableEq, Repr

/-!
The unknown physical quantities and figure observables of the amphitheater
echo experiment.  Riser index `n + 1` denotes the next reflecting face farther
from the stage than riser `n`.

No field assigns a numerical value to `pulsePeriod` or `perceivedFrequency`.
-/
structure AmphitheaterEchoSetup where
  terraceWidth : AcousticLength
  figureWidthLabel : AcousticLength
  soundSpeedInAir : AcousticSpeed
  stageSourcePosition : AxialPosition
  reflectingFacePosition : ℕ → AxialPosition
  pathLength : ℕ → EchoLeg → AcousticLength
  legTravelTime : ℕ → EchoLeg → AcousticDuration
  pulseReturnTime : ℕ → AcousticDuration
  pulsePeriod : AcousticDuration
  perceivedFrequency : AcousticFrequency
  rayDirection : ℕ → EchoLeg → AxialDirection
  rayOrientation : ℕ → EchoLeg → RayOrientation
  figureShowsObject : FigureObject → Bool
  figureShowsLabel : FigureLabel → Bool
  clapSourceIsOnStage : Prop
  oneReturnPulseFromEachRiser : Prop

/-!
Problem-statement and primary-image readouts.  The image identifies the stage,
person, stepped terrace, reflecting vertical risers, and the labels `w` and
`Terrace`.  The problem supplies `w = 0.75 m`, states one return pulse from each
terrace, and asks us to impose the horizontal-ray idealization.

The adjacent-face equation is the geometric content of a common terrace width:
as the index increases, the reflecting face is one width farther to the left
of the source.  No pulse period, frequency, or answer label is fixed here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : AmphitheaterEchoSetup) : Prop where
  figureShowsHandclapper : setup.figureShowsObject .handclapper = true
  figureShowsStage : setup.figureShowsObject .stagePlatform = true
  figureShowsSteppedTerrace : setup.figureShowsObject .steppedTerrace = true
  figureShowsReflectingRisers : setup.figureShowsObject .reflectingRiser = true
  figureShowsWidthLabel : setup.figureShowsLabel .width_w = true
  figureShowsTerraceLabel : setup.figureShowsLabel .terrace = true
  sourceOnStage : setup.clapSourceIsOnStage
  onePulsePerRiser : setup.oneReturnPulseFromEachRiser
  labeledWidthIsTerraceWidth :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.figureWidthLabel =
        lengthReadout unit setup.terraceWidth
  terraceWidthMeters : lengthInMeters setup.terraceWidth = 3 / 4
  stageLiesToRightOfRisers :
    ∀ n, positionInMeters (setup.reflectingFacePosition n) <
      positionInMeters setup.stageSourcePosition
  adjacentRiserSpacing :
    ∀ (unit : LengthUnit) (n : ℕ),
      positionReadout unit (setup.reflectingFacePosition n) -
          positionReadout unit (setup.reflectingFacePosition (n + 1)) =
        lengthReadout unit setup.terraceWidth
  allRaysHorizontal :
    ∀ n leg, setup.rayOrientation n leg = .horizontal
  outboundRaysPointTowardTerrace :
    ∀ n, setup.rayDirection n .outbound = .stageToTerrace
  reflectedRaysPointTowardStage :
    ∀ n, setup.rayDirection n .reflectedReturn = .terraceToStage

/-!
The separate standard room-temperature speed calibration needed to evaluate
the multiple-choice answer.  The source problem itself does not print a speed,
so this datum is not classified as a source or figure readout.
-/
def UsesStandardAirSoundSpeed (setup : AmphitheaterEchoSetup) : Prop :=
  speedInMetersPerSecond setup.soundSpeedInAir = 343

/-- Positivity and nondegeneracy conditions for the idealized echo train. -/
structure HasPhysicalEchoParameters
    (setup : AmphitheaterEchoSetup) : Prop where
  terraceWidthPositive : 0 < lengthInMeters setup.terraceWidth
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeedInAir
  pathLengthsPositive :
    ∀ n leg, 0 < lengthInMeters (setup.pathLength n leg)
  legTimesNonnegative :
    ∀ n leg, 0 ≤ durationInSeconds (setup.legTravelTime n leg)
  returnTimesNonnegative :
    ∀ n, 0 ≤ durationInSeconds (setup.pulseReturnTime n)
  pulsePeriodPositive : 0 < durationInSeconds setup.pulsePeriod
  perceivedFrequencyPositive :
    0 < frequencyInHertz setup.perceivedFrequency

/-!
Governing geometry and propagation laws for the echo train.

For every coherent unit choice, each horizontal leg has length equal to the
stage-to-riser separation, propagation obeys `distance = speed * time`, the
return time is the sum of the two leg times, adjacent returns differ by the
common pulse period, and frequency is reciprocal to that period.  These laws
contain no numerical conclusion for the requested period or frequency.
-/
structure SatisfiesTerraceEchoLaws
    (setup : AmphitheaterEchoSetup) : Prop where
  horizontalPathGeometry :
    ∀ (unit : LengthUnit) (n : ℕ) (leg : EchoLeg),
      lengthReadout unit (setup.pathLength n leg) =
        positionReadout unit setup.stageSourcePosition -
          positionReadout unit (setup.reflectingFacePosition n)
  constantSpeedPropagation :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (n : ℕ) (leg : EchoLeg),
      speedReadout lengthUnit timeUnit setup.soundSpeedInAir *
          durationReadout timeUnit (setup.legTravelTime n leg) =
        lengthReadout lengthUnit (setup.pathLength n leg)
  returnTimeComposition :
    ∀ (unit : TimeUnit) (n : ℕ),
      durationReadout unit (setup.pulseReturnTime n) =
        durationReadout unit (setup.legTravelTime n .outbound) +
          durationReadout unit (setup.legTravelTime n .reflectedReturn)
  periodicAdjacentReturns :
    ∀ (unit : TimeUnit) (n : ℕ),
      durationReadout unit setup.pulsePeriod =
        durationReadout unit (setup.pulseReturnTime (n + 1)) -
          durationReadout unit (setup.pulseReturnTime n)
  pulseFrequencyPeriodRelation :
    ∀ unit : TimeUnit,
      frequencyReadout unit setup.perceivedFrequency *
          durationReadout unit setup.pulsePeriod = 1

/-! ## Derived quantities and displayed answers -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each displayed answer label. -/
def AnswerChoice.hertz : AnswerChoice → ℝ
  | .A => 200
  | .B => 210
  | .C => 220
  | .D => 230

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed answer is uniquely closest to an exact model frequency. -/
def IsClosestAnswerChoice
    (actualHertz : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |actualHertz - choice.hertz| < |actualHertz - other.hertz|

/-!
Horizontal out-and-back propagation makes the path to riser `n + 1` exactly
`2w` longer than the path to riser `n`.
-/
lemma adjacentRoundTripPathIncrementInMeters_eq_twiceWidth
    (setup : AmphitheaterEchoSetup)
    (_readouts : MatchesProblemAndPrimaryFigure setup)
    (_laws : SatisfiesTerraceEchoLaws setup)
    (n : ℕ) :
    (lengthInMeters (setup.pathLength (n + 1) .outbound) +
          lengthInMeters (setup.pathLength (n + 1) .reflectedReturn)) -
        (lengthInMeters (setup.pathLength n .outbound) +
          lengthInMeters (setup.pathLength n .reflectedReturn)) =
      2 * lengthInMeters setup.terraceWidth := by
  have hOutboundNext :=
    _laws.horizontalPathGeometry LengthUnit.meters (n + 1) .outbound
  have hReturnNext :=
    _laws.horizontalPathGeometry LengthUnit.meters (n + 1) .reflectedReturn
  have hOutbound := _laws.horizontalPathGeometry LengthUnit.meters n .outbound
  have hReturn :=
    _laws.horizontalPathGeometry LengthUnit.meters n .reflectedReturn
  have hSpacing := _readouts.adjacentRiserSpacing LengthUnit.meters n
  change
    lengthInMeters (setup.pathLength (n + 1) .outbound) =
      positionInMeters setup.stageSourcePosition -
        positionInMeters (setup.reflectingFacePosition (n + 1)) at hOutboundNext
  change
    lengthInMeters (setup.pathLength (n + 1) .reflectedReturn) =
      positionInMeters setup.stageSourcePosition -
        positionInMeters (setup.reflectingFacePosition (n + 1)) at hReturnNext
  change
    lengthInMeters (setup.pathLength n .outbound) =
      positionInMeters setup.stageSourcePosition -
        positionInMeters (setup.reflectingFacePosition n) at hOutbound
  change
    lengthInMeters (setup.pathLength n .reflectedReturn) =
      positionInMeters setup.stageSourcePosition -
        positionInMeters (setup.reflectingFacePosition n) at hReturn
  change
    positionInMeters (setup.reflectingFacePosition n) -
        positionInMeters (setup.reflectingFacePosition (n + 1)) =
      lengthInMeters setup.terraceWidth at hSpacing
  linarith

/-!
With `w = 3/4 m` and sound speed `343 m/s`, adjacent return pulses are
separated by `2w/v = 3/686 s`.
-/
lemma pulsePeriodInSeconds_eq
    (setup : AmphitheaterEchoSetup)
    (_physical : HasPhysicalEchoParameters setup)
    (_readouts : MatchesProblemAndPrimaryFigure setup)
    (_airData : UsesStandardAirSoundSpeed setup)
    (_laws : SatisfiesTerraceEchoLaws setup) :
    durationInSeconds setup.pulsePeriod = (3 / 686 : ℝ) := by
  have hOutboundZero :=
    _laws.constantSpeedPropagation
      LengthUnit.meters TimeUnit.seconds 0 .outbound
  have hReturnZero :=
    _laws.constantSpeedPropagation
      LengthUnit.meters TimeUnit.seconds 0 .reflectedReturn
  have hOutboundOne :=
    _laws.constantSpeedPropagation
      LengthUnit.meters TimeUnit.seconds (0 + 1) .outbound
  have hReturnOne :=
    _laws.constantSpeedPropagation
      LengthUnit.meters TimeUnit.seconds (0 + 1) .reflectedReturn
  have hCompositionZero :=
    _laws.returnTimeComposition TimeUnit.seconds 0
  have hCompositionOne :=
    _laws.returnTimeComposition TimeUnit.seconds (0 + 1)
  have hPeriod := _laws.periodicAdjacentReturns TimeUnit.seconds 0
  have hPathIncrement :=
    adjacentRoundTripPathIncrementInMeters_eq_twiceWidth
      setup _readouts _laws 0
  change speedInMetersPerSecond setup.soundSpeedInAir = 343 at _airData
  change
    speedInMetersPerSecond setup.soundSpeedInAir *
        durationInSeconds (setup.legTravelTime 0 .outbound) =
      lengthInMeters (setup.pathLength 0 .outbound) at hOutboundZero
  change
    speedInMetersPerSecond setup.soundSpeedInAir *
        durationInSeconds (setup.legTravelTime 0 .reflectedReturn) =
      lengthInMeters (setup.pathLength 0 .reflectedReturn) at hReturnZero
  change
    speedInMetersPerSecond setup.soundSpeedInAir *
        durationInSeconds (setup.legTravelTime (0 + 1) .outbound) =
      lengthInMeters (setup.pathLength (0 + 1) .outbound) at hOutboundOne
  change
    speedInMetersPerSecond setup.soundSpeedInAir *
        durationInSeconds (setup.legTravelTime (0 + 1) .reflectedReturn) =
      lengthInMeters (setup.pathLength (0 + 1) .reflectedReturn) at hReturnOne
  change
    durationInSeconds (setup.pulseReturnTime 0) =
      durationInSeconds (setup.legTravelTime 0 .outbound) +
        durationInSeconds (setup.legTravelTime 0 .reflectedReturn) at hCompositionZero
  change
    durationInSeconds (setup.pulseReturnTime (0 + 1)) =
      durationInSeconds (setup.legTravelTime (0 + 1) .outbound) +
        durationInSeconds (setup.legTravelTime (0 + 1) .reflectedReturn) at hCompositionOne
  change
    durationInSeconds setup.pulsePeriod =
      durationInSeconds (setup.pulseReturnTime (0 + 1)) -
        durationInSeconds (setup.pulseReturnTime 0) at hPeriod
  rw [_airData] at hOutboundZero hReturnZero hOutboundOne hReturnOne
  rw [_readouts.terraceWidthMeters] at hPathIncrement
  norm_num at hOutboundZero hReturnZero hOutboundOne hReturnOne
  norm_num at hCompositionZero hCompositionOne hPeriod hPathIncrement ⊢
  linarith

/-!
The reciprocal of the adjacent-pulse period is the exact model frequency
`686/3 Hz`, approximately `228.67 Hz`.
-/
lemma perceivedFrequencyInHertz_eq
    (setup : AmphitheaterEchoSetup)
    (_physical : HasPhysicalEchoParameters setup)
    (_readouts : MatchesProblemAndPrimaryFigure setup)
    (_airData : UsesStandardAirSoundSpeed setup)
    (_laws : SatisfiesTerraceEchoLaws setup) :
    frequencyInHertz setup.perceivedFrequency = (686 / 3 : ℝ) := by
  have hPeriod :=
    pulsePeriodInSeconds_eq setup _physical _readouts _airData _laws
  have hFrequencyPeriod :=
    _laws.pulseFrequencyPeriodRelation TimeUnit.seconds
  change
    frequencyInHertz setup.perceivedFrequency *
        durationInSeconds setup.pulsePeriod = 1 at hFrequencyPeriod
  rw [hPeriod] at hFrequencyPeriod
  norm_num at hFrequencyPeriod ⊢
  linarith

/-!
The horizontal-ray terrace model gives an exact return frequency of
`686/3 Hz ≈ 228.67 Hz`; among the displayed frequencies, this uniquely selects
the recorded answer D (`230 Hz`).

This formalizes `thm:physics:phyx_mini_0310:target`.
-/
theorem problem_phyx_mini_0310
    (setup : AmphitheaterEchoSetup)
    (_physical : HasPhysicalEchoParameters setup)
    (_readouts : MatchesProblemAndPrimaryFigure setup)
    (_airData : UsesStandardAirSoundSpeed setup)
    (_laws : SatisfiesTerraceEchoLaws setup) :
    frequencyInHertz setup.perceivedFrequency = (686 / 3 : ℝ) ∧
      IsClosestAnswerChoice
        (frequencyInHertz setup.perceivedFrequency)
        recordedDatasetAnswer := by
  have hFrequency :=
    perceivedFrequencyInHertz_eq setup _physical _readouts _airData _laws
  constructor
  · exact hFrequency
  · rw [hFrequency]
    intro other hOther
    cases other with
    | A => norm_num [recordedDatasetAnswer, AnswerChoice.hertz]
    | B => norm_num [recordedDatasetAnswer, AnswerChoice.hertz]
    | C => norm_num [recordedDatasetAnswer, AnswerChoice.hertz]
    | D => exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0310
