import Mathlib.Algebra.Order.Floor.Ring
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Formation of a packed crowd layer at a locked door

An idealized one-dimensional stream of people walks toward a locked door.  In
the supplied top-down figure, each person occupies longitudinal depth `d`, and
each clear interval (including the leading interval to the door) is labeled
`L`.  Once a person reaches the obstruction, people form a stationary,
gap-free layer at the door.

Lengths, elapsed times, and speed are represented by unit-independent Physlib
quantities.  Real numbers occur only as explicitly named unit readouts.  The
number of people already in the layer is discrete, so Mathlib's `Nat.floor` is
used in the uniform-stream law.

Assumption/target boundary:

* `MatchesLockedDoorStreamScenario` records physical object and motion roles;
* `MatchesSuppliedCrowdFigure` records the labels and geometry visible in the
  primary raster;
* `MatchesProblemReadouts` records `vₛ = 3.50 m/s`, `d = 0.25 m`,
  `L = 1.75 m`, and the requested layer depth `5.0 m`;
* `SatisfiesUniformStreamPackingLaws` gives generic initial-spacing,
  arrival-count, and contact-packing laws; and
* first attainment of the requested depth and the answer `10 s` occur only in
  the conclusion of the final theorem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0728

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative elapsed physical time measured from the pictured `t = 0`. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed from Physlib. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({UnitChoices.SI with length := unit} : UnitChoices)).val : ℝ)

/-- Read an elapsed physical time in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration ({UnitChoices.SI with time := unit} : UnitChoices)).val : ℝ)

/-- Read a physical speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed ({UnitChoices.SI with
    length := lengthUnit, time := timeUnit} : UnitChoices)).val : ℝ)

/-- Metre readout used for the corridor geometry and requested layer depth. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout used for elapsed times measured from the pictured instant. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Metres-per-second readout of the common walking speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical roles and primary-figure vocabulary -/

/-- The three people visible in the raster, ordered from left to right. -/
inductive VisiblePerson where
  | rear
  | middle
  | front
  deriving DecidableEq, Fintype, Repr

/-- The three clear intervals visibly marked above the stream. -/
inductive VisibleClearGap where
  | rearToMiddle
  | middleToFront
  | frontToDoor
  deriving DecidableEq, Fintype, Repr

/-- Literal semantic labels appearing in the primary image. -/
inductive FigureLabel where
  | capitalL
  | lowerD
  | lockedDoor
  deriving DecidableEq, Fintype, Repr

/-- Longitudinal directions along the horizontal corridor. -/
inductive CorridorDirection where
  | towardDoor
  | awayFromDoor
  deriving DecidableEq, Repr

/-- Whether the exit door obstructs the stream. -/
inductive DoorState where
  | locked
  | open
  deriving DecidableEq, Repr

/-- Idealized motion regime used before each person joins the layer. -/
inductive StreamMotionModel where
  | commonConstantSpeedUntilBlocked
  deriving DecidableEq, Repr

/-- Idealized configuration of people who have reached the door. -/
inductive LayerPackingModel where
  | stationaryContactWithoutGaps
  deriving DecidableEq, Repr

/-!
Qualitative transcription of `phyx_data/test_image/728.png`.  It distinguishes
the three `L`-marked clear gaps from the three `d`-marked occupied depths.
-/
structure LockedDoorStreamFigure where
  personShown : VisiblePerson → Bool
  motionArrowShown : VisiblePerson → Bool
  motionArrowDirection : VisiblePerson → CorridorDirection
  clearGapShown : VisibleClearGap → Bool
  clearGapLabel : VisibleClearGap → FigureLabel
  occupiedDepthMarked : VisiblePerson → Bool
  occupiedDepthLabel : VisiblePerson → FigureLabel
  doorAtRightEnd : Bool
  doorLabelShown : Bool
  doorLabel : FigureLabel
  topDownCorridorView : Bool

/-!
Independent quantities and observables of the idealized crowd stream.

The natural number index in `initialFrontDistanceToDoor` is zero-based, with
index `0` denoting the leading person.  The two time-dependent observables are
not defined from the answer choice; their behavior is constrained only by the
generic physical laws below.
-/
structure LockedDoorStreamSetup where
  figure : LockedDoorStreamFigure
  doorState : DoorState
  streamDirection : CorridorDirection
  motionModel : StreamMotionModel
  packingModel : LayerPackingModel
  walkingSpeed : SpeedQuantity
  personDepth : LengthQuantity
  clearSeparation : LengthQuantity
  requestedLayerDepth : LengthQuantity
  initialFrontDistanceToDoor : ℕ → LengthQuantity
  packedPeopleAtElapsedTime : DurationQuantity → ℕ
  layerDepthAtElapsedTime : DurationQuantity → LengthQuantity

/-! ## Scenario, figure evidence, and calibrated data -/

/-- Physical roles stated in the prose, independent of all numerical values. -/
structure MatchesLockedDoorStreamScenario
    (setup : LockedDoorStreamSetup) : Prop where
  exitIsLocked : setup.doorState = .locked
  peopleMoveTowardDoor : setup.streamDirection = .towardDoor
  commonUniformWalkingMotion :
    setup.motionModel = .commonConstantSpeedUntilBlocked
  contactLayerAtDoor : setup.packingModel = .stationaryContactWithoutGaps

/-- Qualitative facts and literal labels read from the supplied primary image. -/
structure MatchesSuppliedCrowdFigure
    (setup : LockedDoorStreamSetup) : Prop where
  allThreePeopleShown : ∀ person, setup.figure.personShown person = true
  allThreeMotionArrowsShown :
    ∀ person, setup.figure.motionArrowShown person = true
  allArrowsPointTowardDoor :
    ∀ person, setup.figure.motionArrowDirection person = .towardDoor
  allThreeClearGapsShown :
    ∀ gap, setup.figure.clearGapShown gap = true
  clearGapsCarryCapitalL :
    ∀ gap, setup.figure.clearGapLabel gap = .capitalL
  allThreeOccupiedDepthsMarked :
    ∀ person, setup.figure.occupiedDepthMarked person = true
  occupiedDepthsCarryLowerD :
    ∀ person, setup.figure.occupiedDepthLabel person = .lowerD
  doorIsAtRightEnd : setup.figure.doorAtRightEnd = true
  lockedDoorTextShown : setup.figure.doorLabelShown = true
  doorTextIsLockedDoor : setup.figure.doorLabel = .lockedDoor
  imageIsTopDownCorridorView : setup.figure.topDownCorridorView = true

/-!
The numerical values supplied in the question.  The `5 m` value specifies
which depth is being asked about; it does not specify when that depth occurs.
-/
structure MatchesProblemReadouts (setup : LockedDoorStreamSetup) : Prop where
  walkingSpeedMetersPerSecond :
    speedInMetersPerSecond setup.walkingSpeed = (7 : ℝ) / 2
  personDepthMeters :
    lengthInMeters setup.personDepth = (1 : ℝ) / 4
  clearSeparationMeters :
    lengthInMeters setup.clearSeparation = (7 : ℝ) / 4
  requestedLayerDepthMeters :
    lengthInMeters setup.requestedLayerDepth = 5

/-- Positivity conditions selecting the physically meaningful branch. -/
structure HasPhysicalStreamParameters
    (setup : LockedDoorStreamSetup) : Prop where
  walkingSpeedPositive : ∀ lengthUnit timeUnit,
    0 < speedReadout lengthUnit timeUnit setup.walkingSpeed
  personDepthPositive : ∀ unit,
    0 < lengthReadout unit setup.personDepth
  clearSeparationPositive : ∀ unit,
    0 < lengthReadout unit setup.clearSeparation
  requestedLayerDepthPositive : ∀ unit,
    0 < lengthReadout unit setup.requestedLayerDepth

/-! ## Uniform-stream and locked-door packing laws -/

/-!
Generic laws for the idealized stream.  At the pictured initial instant, the
front of person `n` is `(n+1)L + n d` from the door.  Because all people move
together until blocked, a new person joins the stationary layer after every
additional travel distance `L`.  The floor therefore counts completed
arrivals, while the contact-packed layer has one body depth per arrival.

These laws contain neither the requested five-metre threshold nor the
ten-second answer.
-/
structure SatisfiesUniformStreamPackingLaws
    (setup : LockedDoorStreamSetup) : Prop where
  initialUniformGeometry : ∀ (n : ℕ) (unit : LengthUnit),
    lengthReadout unit (setup.initialFrontDistanceToDoor n) =
      ((n : ℝ) + 1) * lengthReadout unit setup.clearSeparation +
        (n : ℝ) * lengthReadout unit setup.personDepth
  packedCountFromUniformMotion :
    ∀ (elapsed : DurationQuantity)
      (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      setup.packedPeopleAtElapsedTime elapsed =
        ⌊speedReadout lengthUnit timeUnit setup.walkingSpeed *
            durationReadout timeUnit elapsed /
            lengthReadout lengthUnit setup.clearSeparation⌋₊
  layerDepthFromContactPacking :
    ∀ (elapsed : DurationQuantity) (unit : LengthUnit),
      lengthReadout unit (setup.layerDepthAtElapsedTime elapsed) =
        (setup.packedPeopleAtElapsedTime elapsed : ℝ) *
          lengthReadout unit setup.personDepth

/-! ## Target relation -/

/-!
An elapsed time is the first time the layer reaches the requested depth when
the depth equals the requested value then and is strictly smaller at every
earlier physical duration.  Durations are nonnegative by their `NNReal`
representation.
-/
def IsFirstTimeLayerReachesRequestedDepth
    (setup : LockedDoorStreamSetup) (elapsed : DurationQuantity) : Prop :=
  lengthInMeters (setup.layerDepthAtElapsedTime elapsed) =
      lengthInMeters setup.requestedLayerDepth ∧
    ∀ earlier : DurationQuantity,
      durationInSeconds earlier < durationInSeconds elapsed →
        lengthInMeters (setup.layerDepthAtElapsedTime earlier) <
          lengthInMeters setup.requestedLayerDepth

/--
With the pictured gap convention and the supplied data, twenty body depths
make the requested five-metre layer, and the twentieth arrival occurs at ten
seconds.  Thus the first elapsed time at which the layer reaches the requested
depth has the recorded answer-choice value `10 s`.

Blueprint: `thm:physics:phyx_mini_0728:target`.
-/
theorem layer_depth_reaches_five_meters_at_ten_seconds
    (setup : LockedDoorStreamSetup)
    (hScenario : MatchesLockedDoorStreamScenario setup)
    (hFigure : MatchesSuppliedCrowdFigure setup)
    (hData : MatchesProblemReadouts setup)
    (hPositive : HasPhysicalStreamParameters setup)
    (hPhysics : SatisfiesUniformStreamPackingLaws setup) :
    ∃ elapsed : DurationQuantity,
      IsFirstTimeLayerReachesRequestedDepth setup elapsed ∧
        durationInSeconds elapsed = 10 := by
  let elapsed : DurationQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨10⟩ : WithDim T𝓭 NNReal)
  have hElapsed : durationInSeconds elapsed = 10 := by
    norm_num [elapsed, durationInSeconds, durationReadout,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self]
    change UnitChoices.SI.dimScale UnitChoices.SI T𝓭 = 1
    exact UnitChoices.dimScale_self _ _
  have hSpeed :
      speedReadout LengthUnit.meters TimeUnit.seconds setup.walkingSpeed =
        (7 : ℝ) / 2 := by
    simpa [speedInMetersPerSecond] using hData.walkingSpeedMetersPerSecond
  have hDepth :
      lengthReadout LengthUnit.meters setup.personDepth = (1 : ℝ) / 4 := by
    simpa [lengthInMeters] using hData.personDepthMeters
  have hSeparation :
      lengthReadout LengthUnit.meters setup.clearSeparation = (7 : ℝ) / 4 := by
    simpa [lengthInMeters] using hData.clearSeparationMeters
  have hRequested :
      lengthReadout LengthUnit.meters setup.requestedLayerDepth = 5 := by
    simpa [lengthInMeters] using hData.requestedLayerDepthMeters
  have hElapsedReadout :
      durationReadout TimeUnit.seconds elapsed = 10 := by
    simpa [durationInSeconds] using hElapsed
  have hCount : setup.packedPeopleAtElapsedTime elapsed = 20 := by
    rw [hPhysics.packedCountFromUniformMotion elapsed
      LengthUnit.meters TimeUnit.seconds]
    rw [hSpeed, hElapsedReadout, hSeparation]
    norm_num
  have hLayer :
      lengthInMeters (setup.layerDepthAtElapsedTime elapsed) = 5 := by
    change lengthReadout LengthUnit.meters
      (setup.layerDepthAtElapsedTime elapsed) = 5
    rw [hPhysics.layerDepthFromContactPacking elapsed LengthUnit.meters,
      hCount, hDepth]
    norm_num
  refine ⟨elapsed, ?_, hElapsed⟩
  constructor
  · rw [hLayer, hData.requestedLayerDepthMeters]
  · intro earlier hEarlier
    have hEarlierSeconds :
        durationReadout TimeUnit.seconds earlier < 10 := by
      rw [hElapsed] at hEarlier
      simpa [durationInSeconds] using hEarlier
    have hEarlierNonnegative :
        0 ≤ durationReadout TimeUnit.seconds earlier := by
      exact NNReal.coe_nonneg _
    have hCountLt : setup.packedPeopleAtElapsedTime earlier < 20 := by
      rw [hPhysics.packedCountFromUniformMotion earlier
        LengthUnit.meters TimeUnit.seconds]
      have hExpressionNonnegative :
          0 ≤ speedReadout LengthUnit.meters TimeUnit.seconds
              setup.walkingSpeed *
            durationReadout TimeUnit.seconds earlier /
            lengthReadout LengthUnit.meters setup.clearSeparation := by
        rw [hSpeed, hSeparation]
        positivity
      apply (Nat.floor_lt hExpressionNonnegative).2
      rw [hSpeed, hSeparation]
      norm_num
      linarith
    change lengthReadout LengthUnit.meters
      (setup.layerDepthAtElapsedTime earlier) <
        lengthReadout LengthUnit.meters setup.requestedLayerDepth
    rw [hPhysics.layerDepthFromContactPacking earlier LengthUnit.meters,
      hDepth, hRequested]
    have hCountLtReal :
        (setup.packedPeopleAtElapsedTime earlier : ℝ) < 20 := by
      exact_mod_cast hCountLt
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0728
