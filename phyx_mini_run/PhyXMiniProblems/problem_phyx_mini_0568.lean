import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0568

open Dimension

/-!
# Light travel times from the midpoint of a moving rocket

A rocket of proper length `L₀ = 240 m` moves to the right at `0.6 c`
relative to ground observer `O`. Observer `O'` is at rest with the rocket.
The source at midpoint `B` emits one flash toward tail mirror `A` and one
toward nose mirror `C`; each flash is reflected and later absorbed at `B`.

Lengths, times, and speeds below are unit-independent Physlib quantities.
Real numbers occur only as named-unit readouts, a dimensionless speed ratio,
and the displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A coordinate-time reading or elapsed duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A signed physical speed along the common longitudinal axis. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a time quantity in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time {UnitChoices.SI with time := unit}).val

/-- Read a speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  (speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Metre readout used for the stated proper length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Microsecond readout used by the four answer choices. -/
def timeInMicroseconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.microseconds time

/-- Metre-per-microsecond readout of a signed speed. -/
def speedInMetersPerMicrosecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.microseconds speed

/-- Physlib's exact vacuum light speed, read in metres per microsecond. -/
def vacuumLightSpeedInMetersPerMicrosecond : ℝ :=
  speedInMetersPerMicrosecond DimSpeed.speedOfLight

/-! ## Frames, rocket points, flash events, and figure labels -/

/-- The ground frame `O` and the rocket rest frame `O'`. -/
inductive InertialFrameLabel where
  | groundO
  | rocketOPrime
  deriving DecidableEq, Fintype, Repr

/-- The two observers named in the problem and shown in the figure. -/
inductive ObserverLabel where
  | O
  | OPrime
  deriving DecidableEq, Fintype, Repr

/-- The labeled rocket points: tail mirror `A`, source `B`, and nose mirror `C`. -/
inductive RocketPointLabel where
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- The two flashes are distinguished by which mirror they approach first. -/
inductive FlashLabel where
  | towardTail
  | towardNose
  deriving DecidableEq, Fintype, Repr

/-- The three successive events tracked for each flash. -/
inductive FlashEvent where
  | emission
  | reflectionAtMirror
  | absorptionAtSource
  deriving DecidableEq, Fintype, Repr

/-- Directions along the common horizontal axis. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Coordinate axes explicitly drawn for the two frames. -/
inductive FigureAxis where
  | x
  | y
  | xPrime
  | yPrime
  deriving DecidableEq, Fintype, Repr

/-- Literal textual labels visible in figure 17.4. -/
inductive FigureTextLabel where
  | originO
  | originOPrime
  | pointA
  | pointB
  | pointC
  | velocityV
  | fullLengthL0
  | halfLengthL0OverTwo
  | xEqualsXPrime
  deriving DecidableEq, Fintype, Repr

/-- The three longitudinal segments whose lengths are annotated in the figure. -/
inductive FigureSegment where
  | AtoB
  | BtoC
  | AtoC
  deriving DecidableEq, Fintype, Repr

/-- Symbolic length annotations printed beside the red dimension arrows. -/
inductive FigureDistanceLabel where
  | L0
  | L0OverTwo
  deriving DecidableEq, Repr

/--
Primary-image information: axes, origins, point ordering, velocity arrow, and
the `L₀` and `L₀/2` annotations. It contains no travel-time readout.
-/
structure RocketLightFigure where
  axisShown : FigureAxis → Bool
  textLabelShown : FigureTextLabel → Bool
  distanceLabel : FigureSegment → FigureDistanceLabel
  velocityArrowDirection : HorizontalDirection
  pointsOrderedLeftToRightAsABC : Bool
  xAxesAreCoincident : Bool
  originOIsLeftOfOriginOPrime : Bool
  rocketDrawnAlongCommonHorizontalAxis : Bool

/-!
The independent physical data of the experiment. The outbound and return
durations are unknown physical quantities. They are constrained only by the
general light-propagation laws below, rather than defined from an answer.
-/
structure RocketLightTravelSetup where
  observerFrame : ObserverLabel → InertialFrameLabel
  rocketRestFrame : InertialFrameLabel
  groundRestFrame : InertialFrameLabel
  rocketMotionDirectionInO : HorizontalDirection
  sourcePoint : RocketPointLabel
  mirrorPoint : FlashLabel → RocketPointLabel
  flashDirectionInOPrime : FlashLabel → HorizontalDirection
  eventLocation : FlashLabel → FlashEvent → RocketPointLabel
  eventTimeInOPrime : FlashLabel → FlashEvent → TimeQuantity
  rocketProperLength_L0 : LengthQuantity
  sourceToMirrorDistance : FlashLabel → LengthQuantity
  rocketSpeedRelativeToO : SpeedQuantity
  /-- The dimensionless speed ratio `β = V/c`. -/
  speedFractionOfLight : ℝ
  outboundTimeToMirrorInOPrime : FlashLabel → TimeQuantity
  returnTimeToSourceInOPrime : FlashLabel → TimeQuantity
  figure : RocketLightFigure

/-! ## Scenario facts, figure evidence, and supplied data -/

/-!
Frame assignments, physical roles, flash directions, and event incidences
from the prose. Simultaneous emission is stated as an event fact in `O'`.
-/
structure MatchesRocketLightScenario
    (setup : RocketLightTravelSetup) : Prop where
  observerOUsesGroundFrame :
    setup.observerFrame .O = .groundO
  observerOPrimeUsesRocketFrame :
    setup.observerFrame .OPrime = .rocketOPrime
  rocketIsAtRestInOPrime :
    setup.rocketRestFrame = .rocketOPrime
  groundIsAtRestInO :
    setup.groundRestFrame = .groundO
  rocketMovesRightwardInO :
    setup.rocketMotionDirectionInO = .rightward
  sourceIsPointB : setup.sourcePoint = .B
  tailMirrorIsPointA : setup.mirrorPoint .towardTail = .A
  noseMirrorIsPointC : setup.mirrorPoint .towardNose = .C
  tailFlashMovesLeftward :
    setup.flashDirectionInOPrime .towardTail = .leftward
  noseFlashMovesRightward :
    setup.flashDirectionInOPrime .towardNose = .rightward
  eachFlashIsEmittedAtSource : ∀ flash,
    setup.eventLocation flash .emission = setup.sourcePoint
  eachFlashIsReflectedAtItsMirror : ∀ flash,
    setup.eventLocation flash .reflectionAtMirror = setup.mirrorPoint flash
  eachFlashIsAbsorbedAtSource : ∀ flash,
    setup.eventLocation flash .absorptionAtSource = setup.sourcePoint
  flashesAreEmittedSimultaneously : ∀ unit : TimeUnit,
    timeReadout unit
        (setup.eventTimeInOPrime .towardTail .emission) =
      timeReadout unit
        (setup.eventTimeInOPrime .towardNose .emission)

/-- Exact qualitative and symbolic information transcribed from the image. -/
structure MatchesSuppliedRocketLightFigure
    (setup : RocketLightTravelSetup) : Prop where
  everyAxisIsShown :
    ∀ axis, setup.figure.axisShown axis = true
  everyTextLabelIsShown :
    ∀ label, setup.figure.textLabelShown label = true
  segmentABIsLabelledHalfLength :
    setup.figure.distanceLabel .AtoB = .L0OverTwo
  segmentBCIsLabelledHalfLength :
    setup.figure.distanceLabel .BtoC = .L0OverTwo
  segmentACIsLabelledFullLength :
    setup.figure.distanceLabel .AtoC = .L0
  velocityArrowPointsRight :
    setup.figure.velocityArrowDirection = .rightward
  pointsAreOrderedABC :
    setup.figure.pointsOrderedLeftToRightAsABC = true
  xAndXPrimeAreCoincident :
    setup.figure.xAxesAreCoincident = true
  groundOriginIsLeftOfRocketOrigin :
    setup.figure.originOIsLeftOfOriginOPrime = true
  rocketLiesAlongCommonAxis :
    setup.figure.rocketDrawnAlongCommonHorizontalAxis = true

/-!
The numerical readouts stated in the problem: `L₀ = 240 m` and
`V = 0.6c = (3/5)c`. The speed relation is required in every compatible
pair of length and time units; it does not determine either requested time.
-/
structure MatchesProblemReadouts
    (setup : RocketLightTravelSetup) : Prop where
  properLengthIs240Meters :
    lengthInMeters setup.rocketProperLength_L0 = 240
  speedFractionIsPointSix :
    setup.speedFractionOfLight = 3 / 5
  speedIsGivenFractionOfVacuumLightSpeed :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.rocketSpeedRelativeToO =
        setup.speedFractionOfLight *
          speedReadout lengthUnit timeUnit DimSpeed.speedOfLight

/-!
The source is midway between the mirrors in the rocket rest frame. Thus
both physical source-to-mirror distances are half the proper rocket length.
This is figure/scenario geometry, not a travel-time conclusion.
-/
structure SatisfiesMidpointGeometry
    (setup : RocketLightTravelSetup) : Prop where
  eachMirrorIsHalfProperLengthFromSource :
    ∀ (flash : FlashLabel) (unit : LengthUnit),
      lengthReadout unit (setup.sourceToMirrorDistance flash) =
        lengthReadout unit setup.rocketProperLength_L0 / 2

/-- Positivity, subluminality, and chronological order of both flash paths. -/
structure HasPhysicalRocketLightParameters
    (setup : RocketLightTravelSetup) : Prop where
  properLengthPositive :
    0 < lengthInMeters setup.rocketProperLength_L0
  eachSourceMirrorDistancePositive : ∀ flash,
    0 < lengthInMeters (setup.sourceToMirrorDistance flash)
  relativeSpeedPositive :
    0 < speedInMetersPerMicrosecond setup.rocketSpeedRelativeToO
  speedFractionNonnegative :
    0 ≤ setup.speedFractionOfLight
  speedFractionSubluminal :
    setup.speedFractionOfLight < 1
  eachFlashReflectsAfterEmission : ∀ flash,
    timeInMicroseconds (setup.eventTimeInOPrime flash .emission) <
      timeInMicroseconds (setup.eventTimeInOPrime flash .reflectionAtMirror)
  eachFlashIsAbsorbedAfterReflection : ∀ flash,
    timeInMicroseconds (setup.eventTimeInOPrime flash .reflectionAtMirror) <
      timeInMicroseconds (setup.eventTimeInOPrime flash .absorptionAtSource)
  eachOutboundDurationPositive : ∀ flash,
    0 < timeInMicroseconds (setup.outboundTimeToMirrorInOPrime flash)
  eachReturnDurationPositive : ∀ flash,
    0 < timeInMicroseconds (setup.returnTimeToSourceInOPrime flash)

/-! ## Governing measurement and light-propagation laws -/

/-!
Elapsed times are event-time differences in `O'`. On both the outgoing and
returning legs, the source--mirror distance equals the invariant vacuum light
speed times the elapsed rocket-frame time. These general laws mention neither
`0.4 μs` nor any answer label.
-/
structure SatisfiesRocketFrameLightPropagation
    (setup : RocketLightTravelSetup) : Prop where
  outboundTimeIsEventDifference :
    ∀ (flash : FlashLabel) (unit : TimeUnit),
      timeReadout unit (setup.outboundTimeToMirrorInOPrime flash) =
        timeReadout unit
            (setup.eventTimeInOPrime flash .reflectionAtMirror) -
          timeReadout unit
            (setup.eventTimeInOPrime flash .emission)
  returnTimeIsEventDifference :
    ∀ (flash : FlashLabel) (unit : TimeUnit),
      timeReadout unit (setup.returnTimeToSourceInOPrime flash) =
        timeReadout unit
            (setup.eventTimeInOPrime flash .absorptionAtSource) -
          timeReadout unit
            (setup.eventTimeInOPrime flash .reflectionAtMirror)
  outboundDistanceIsLightSpeedTimesTime :
    ∀ (flash : FlashLabel) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      lengthReadout lengthUnit (setup.sourceToMirrorDistance flash) =
        speedReadout lengthUnit timeUnit DimSpeed.speedOfLight *
          timeReadout timeUnit
            (setup.outboundTimeToMirrorInOPrime flash)
  returnDistanceIsLightSpeedTimesTime :
    ∀ (flash : FlashLabel) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      lengthReadout lengthUnit (setup.sourceToMirrorDistance flash) =
        speedReadout lengthUnit timeUnit DimSpeed.speedOfLight *
          timeReadout timeUnit
            (setup.returnTimeToSourceInOPrime flash)

/-! ## Answer choices and current target -/

/-- Labels of the four microsecond-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Time in microseconds displayed beside each answer label. -/
def displayedTimeInMicroseconds : AnswerChoice → ℝ
  | .A => 11 / 20
  | .B => 2 / 5
  | .C => 19 / 20
  | .D => 51 / 5

/-- The answer label recorded by the source dataset, retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
Agreement with a displayed microsecond value to within `0.005 μs`, enough
to interpret the finite-precision choices without replacing the exact value.
-/
def AgreesWithDisplayedMicrosecondValue
    (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-- Both rocket-frame outbound durations agree with one displayed choice. -/
def MatchesAnswerChoice
    (setup : RocketLightTravelSetup) (choice : AnswerChoice) : Prop :=
  ∀ flash : FlashLabel,
    AgreesWithDisplayedMicrosecondValue
      (timeInMicroseconds
        (setup.outboundTimeToMirrorInOPrime flash))
      (displayedTimeInMicroseconds choice)

/-!
The midpoint geometry and invariant light-speed law give `(L₀/2)/c` for
each outbound leg. This proof-route lemma has no separate blueprint label.
-/
lemma outboundTravelTimeFormula
    (setup : RocketLightTravelSetup)
    (hGeometry : SatisfiesMidpointGeometry setup)
    (hPhysical : HasPhysicalRocketLightParameters setup)
    (hLight : SatisfiesRocketFrameLightPropagation setup) :
    ∀ flash : FlashLabel,
      timeInMicroseconds
          (setup.outboundTimeToMirrorInOPrime flash) =
        (lengthInMeters setup.rocketProperLength_L0 / 2) /
          vacuumLightSpeedInMetersPerMicrosecond := by
  intro flash
  have hGeometryMeters :=
    hGeometry.eachMirrorIsHalfProperLengthFromSource flash LengthUnit.meters
  have hPropagation :=
    hLight.outboundDistanceIsLightSpeedTimesTime
      flash LengthUnit.meters TimeUnit.microseconds
  change
    lengthReadout LengthUnit.meters (setup.sourceToMirrorDistance flash) =
      vacuumLightSpeedInMetersPerMicrosecond *
        timeInMicroseconds
          (setup.outboundTimeToMirrorInOPrime flash) at hPropagation
  rw [hGeometryMeters] at hPropagation
  have hLightSpeedNeZero :
      vacuumLightSpeedInMetersPerMicrosecond ≠ 0 := by
    simp [vacuumLightSpeedInMetersPerMicrosecond,
      speedInMetersPerMicrosecond, speedReadout,
      DimSpeed.speedOfLight, CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_ne_zero]
  rw [eq_div_iff hLightSpeedNeZero]
  simpa [lengthInMeters, mul_comm] using hPropagation.symm

/-!
Since `L₀/2 = 120 m`, each flash reaches its mirror after
`120 / 299.792458 ≈ 0.40028 μs` in `O'`. Therefore the uniquely matching
display is `0.4 μs`, answer B. The rocket's `0.6c` motion relative to `O`
does not enter this rest-frame light-clock calculation.

This formalizes `thm:physics:phyx_mini_0568:target`. No premise structure
states the exact outbound-time formula, the displayed value, or answer B.
-/
theorem problem_phyx_mini_0568
    (setup : RocketLightTravelSetup)
    (hScenario : MatchesRocketLightScenario setup)
    (hFigure : MatchesSuppliedRocketLightFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : SatisfiesMidpointGeometry setup)
    (hPhysical : HasPhysicalRocketLightParameters setup)
    (hLight : SatisfiesRocketFrameLightPropagation setup) :
    (∀ flash : FlashLabel,
      timeInMicroseconds
          (setup.outboundTimeToMirrorInOPrime flash) =
        120 / vacuumLightSpeedInMetersPerMicrosecond) ∧
      MatchesAnswerChoice setup .B ∧
      ∀ choice : AnswerChoice,
        MatchesAnswerChoice setup choice → choice = .B := by
  have hLightSpeed :
      vacuumLightSpeedInMetersPerMicrosecond =
        (149896229 : ℝ) / 500000 := by
    simp [vacuumLightSpeedInMetersPerMicrosecond,
      speedInMetersPerMicrosecond, speedReadout, DimSpeed.speedOfLight,
      CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale,
      TimeUnit.microseconds]
    rw [NNReal.rpow_neg_one]
    simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_inv]
    change
      ((10 : ℝ) ^ 6)⁻¹ * 299792458 =
        (149896229 : ℝ) / 500000
    norm_num
  have hFormula :=
    outboundTravelTimeFormula setup hGeometry hPhysical hLight
  have hExact : ∀ flash : FlashLabel,
      timeInMicroseconds
          (setup.outboundTimeToMirrorInOPrime flash) =
        (60000000 : ℝ) / 149896229 := by
    intro flash
    rw [hFormula flash, hReadouts.properLengthIs240Meters, hLightSpeed]
    norm_num
  constructor
  · intro flash
    rw [hFormula flash, hReadouts.properLengthIs240Meters]
    norm_num
  constructor
  · intro flash
    rw [hExact flash]
    change |(60000000 : ℝ) / 149896229 - 2 / 5| < 1 / 200
    norm_num [abs_of_nonneg]
  · intro choice hChoice
    cases choice with
    | A =>
        have h := hChoice FlashLabel.towardTail
        rw [hExact .towardTail] at h
        change
          |(60000000 : ℝ) / 149896229 - 11 / 20| < 1 / 200 at h
        norm_num [abs_of_nonpos] at h
    | B => rfl
    | C =>
        have h := hChoice FlashLabel.towardTail
        rw [hExact .towardTail] at h
        change
          |(60000000 : ℝ) / 149896229 - 19 / 20| < 1 / 200 at h
        norm_num [abs_of_nonpos] at h
    | D =>
        have h := hChoice FlashLabel.towardTail
        rw [hExact .towardTail] at h
        change
          |(60000000 : ℝ) / 149896229 - 51 / 5| < 1 / 200 at h
        norm_num [abs_of_nonpos] at h

end PhyXMiniProblems.ProblemPhyXMini0568
