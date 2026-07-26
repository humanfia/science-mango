import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Canoe displacement while a woman walks from start to finish

A `45.0 kg` woman walks inside a `60.0 kg`, `5.00 m` canoe.  The primary
image orders the four stations left end, Start, Finish, and right end, and
labels their successive separations `1.00 m`, `3.00 m`, and `1.00 m`.

Masses, nonnegative lengths, and signed horizontal displacements are modeled
as unit-independent Physlib quantities.  Real numbers occur only as coherent
SI readouts and displayed answer values.  Positive displacement points from
Start toward Finish (to the right in the supplied image).

Assumption/target boundary:

* `MatchesProblemReadouts` contains the two masses and total canoe length.
* `MatchesPrimaryFigure` contains only the visible labels, ordering, and the
  three displayed segment lengths.
* `MatchesCanoeWalkScenario` contains the start/finish roles, initial rest,
  and the instruction to neglect resistance.
* `SatisfiesRigidCanoeKinematics` relates the woman's ground displacement to
  her `3 m` displacement relative to the canoe.
* `SatisfiesIsolatedHorizontalCenterOfMassLaw` states the mass-weighted
  displacement balance for an initially resting system with no external
  horizontal impulse.
* The signed canoe displacement, its travel distance, and selection of answer
  B occur only in the conclusion of `problem_phyx_mini_0769`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0769

open Dimension

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A unit-independent nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A unit-independent nonnegative physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed one-dimensional displacement along the canoe's horizontal axis. -/
abbrev HorizontalDisplacementQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Signed coherent-SI metre readout along the image's horizontal axis. -/
def displacementInMeters
    (displacement : HorizontalDisplacementQuantity) : ℝ :=
  (displacement UnitChoices.SI).val

/-! ## Physical roles and primary-image labels -/

/-- The four geometrically distinguished stations along the canoe. -/
inductive CanoeStation where
  | leftEnd
  | start
  | finish
  | rightEnd
  deriving DecidableEq, Fintype, Repr

/-- The three successive length annotations under the canoe. -/
inductive FigureSegment where
  | leftEndToStart
  | startToFinish
  | finishToRightEnd
  deriving DecidableEq, Fintype, Repr

/-- Endpoints associated with each of the three displayed dimension segments. -/
def FigureSegment.endpoints :
    FigureSegment → CanoeStation × CanoeStation
  | .leftEndToStart => (.leftEnd, .start)
  | .startToFinish => (.start, .finish)
  | .finishToRightEnd => (.finish, .rightEnd)

/-- Qualitative horizontal directions in the supplied image. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Exactly the two interior stations have printed text labels in the image. -/
def stationHasPrintedText : CanoeStation → Bool
  | .leftEnd => false
  | .start => true
  | .finish => true
  | .rightEnd => false

/-- Literal and qualitative content transcribed from image `769.png`. -/
structure CanoeWalkFigure where
  showsWoman : Bool
  showsCanoe : Bool
  showsWater : Bool
  showsHorizontalDimensionLine : Bool
  showsStationText : CanoeStation → Bool
  showsDimensionSegment : FigureSegment → Bool
  stationsFromLeftToRight : List CanoeStation

/-!
Independent physical quantities and scenario roles.  In particular, neither
horizontal displacement is defined from the numerical answer; the governing
relations below constrain both displacement fields.
-/
structure CanoeWalkSetup where
  figure : CanoeWalkFigure
  womanMass : MassQuantity
  canoeMass : MassQuantity
  canoeLength : LengthMagnitude
  displayedSegmentLength : FigureSegment → LengthMagnitude
  womanInitialStation : CanoeStation
  womanFinalStation : CanoeStation
  womanWalkingDirection : HorizontalDirection
  womanGroundDisplacement : HorizontalDisplacementQuantity
  canoeGroundDisplacement : HorizontalDisplacementQuantity
  womanInitiallyStanding : Bool
  systemInitiallyAtRest : Bool
  resistanceToCanoeMotionIgnored : Bool

/-! ## Scenario, data, figure evidence, and governing laws -/

/-- Qualitative scenario conditions stated or physically implicit in the problem. -/
structure MatchesCanoeWalkScenario (setup : CanoeWalkSetup) : Prop where
  womanStartsAtStart : setup.womanInitialStation = .start
  womanFinishesAtFinish : setup.womanFinalStation = .finish
  womanWalksTowardRight : setup.womanWalkingDirection = .right
  womanIsInitiallyStanding : setup.womanInitiallyStanding = true
  isolatedSystemInitiallyAtRest : setup.systemInitiallyAtRest = true
  waterResistanceIsIgnored : setup.resistanceToCanoeMotionIgnored = true

/-- Numerical mass and total-length readouts from the problem prose. -/
structure MatchesProblemReadouts (setup : CanoeWalkSetup) : Prop where
  womanMassKilograms : massInKilograms setup.womanMass = 45
  canoeMassKilograms : massInKilograms setup.canoeMass = 60
  canoeLengthMeters : lengthInMeters setup.canoeLength = 5

/-!
Primary-image evidence.  The dimension line is a measurement line, not a
claim about the canoe's direction of motion.  No canoe displacement or answer
choice occurs in this record.
-/
structure MatchesPrimaryFigure (setup : CanoeWalkSetup) : Prop where
  womanShown : setup.figure.showsWoman = true
  canoeShown : setup.figure.showsCanoe = true
  waterShown : setup.figure.showsWater = true
  horizontalDimensionLineShown :
    setup.figure.showsHorizontalDimensionLine = true
  printedStationTextMatchesImage :
    ∀ station,
      setup.figure.showsStationText station = stationHasPrintedText station
  everyDimensionSegmentShown :
    ∀ segment, setup.figure.showsDimensionSegment segment = true
  displayedStationOrder :
    setup.figure.stationsFromLeftToRight =
      [.leftEnd, .start, .finish, .rightEnd]
  leftInsetMeters :
    lengthInMeters
        (setup.displayedSegmentLength .leftEndToStart) = 1
  walkingSpanMeters :
    lengthInMeters
        (setup.displayedSegmentLength .startToFinish) = 3
  rightInsetMeters :
    lengthInMeters
        (setup.displayedSegmentLength .finishToRightEnd) = 1
  displayedSegmentsPartitionCanoe :
    lengthInMeters
          (setup.displayedSegmentLength .leftEndToStart) +
        lengthInMeters
          (setup.displayedSegmentLength .startToFinish) +
        lengthInMeters
          (setup.displayedSegmentLength .finishToRightEnd) =
      lengthInMeters setup.canoeLength

/-!
Rigid-body translation of the canoe makes the woman's ground displacement
equal to the canoe displacement plus her displacement relative to the canoe.
This is a kinematic law, not the requested canoe displacement formula.
-/
structure SatisfiesRigidCanoeKinematics (setup : CanoeWalkSetup) : Prop where
  relativeWalkDisplacement :
    displacementInMeters setup.womanGroundDisplacement -
        displacementInMeters setup.canoeGroundDisplacement =
      lengthInMeters
        (setup.displayedSegmentLength .startToFinish)

/-!
For the initially resting woman--canoe system with no external horizontal
impulse, conservation of horizontal momentum leaves the center of mass fixed.
The resulting first-moment balance is stated directly because the searched
rigid-body APIs do not provide a two-body, finite-walk interface with these
dimensionful observables.
-/
structure SatisfiesIsolatedHorizontalCenterOfMassLaw
    (setup : CanoeWalkSetup) : Prop where
  massWeightedDisplacementBalance :
    massInKilograms setup.womanMass *
          displacementInMeters setup.womanGroundDisplacement +
        massInKilograms setup.canoeMass *
          displacementInMeters setup.canoeGroundDisplacement = 0

/-! ## Displayed answers and conclusion-side predicates -/

/-- The four distance values printed in the multiple-choice list, in metres. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed distance in metres associated with each supplied answer choice. -/
def displayedDistanceInMeters : AnswerChoice → ℝ
  | .A => 187 / 100
  | .B => 129 / 100
  | .C => 12 / 100
  | .D => 98 / 100

/-- Distance traveled by the canoe, obtained from its signed displacement. -/
def canoeTravelDistanceInMeters (setup : CanoeWalkSetup) : ℝ :=
  |displacementInMeters setup.canoeGroundDisplacement|

/-- Agreement of an exact metre value with a value displayed to hundredths. -/
def AgreesWithDisplayedHundredth (exact displayed : ℝ) : Prop :=
  |exact - displayed| < 1 / 200

/-- A choice is uniquely closest to the exact distance among the four options. -/
def IsUniqueClosestDistanceChoice
    (exact : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |exact - displayedDistanceInMeters choice| <
      |exact - displayedDistanceInMeters other|

/-!
With positive direction from Start to Finish, the canoe moves oppositely by
`9/7 m`; hence it travels `9/7 m`, which displays as `1.29 m` and uniquely
selects answer B.

This declaration formalizes
`thm:physics:phyx_mini_0769:target`.
-/
theorem problem_phyx_mini_0769
    (setup : CanoeWalkSetup)
    (_scenario : MatchesCanoeWalkScenario setup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryFigure setup)
    (_kinematics : SatisfiesRigidCanoeKinematics setup)
    (_centerOfMass : SatisfiesIsolatedHorizontalCenterOfMassLaw setup) :
    displacementInMeters setup.canoeGroundDisplacement = -(9 / 7) ∧
      canoeTravelDistanceInMeters setup = 9 / 7 ∧
      AgreesWithDisplayedHundredth
        (canoeTravelDistanceInMeters setup)
        (displayedDistanceInMeters .B) ∧
      IsUniqueClosestDistanceChoice
        (canoeTravelDistanceInMeters setup) .B := by
  have hkinematics := _kinematics.relativeWalkDisplacement
  have hbalance := _centerOfMass.massWeightedDisplacementBalance
  rw [_figure.walkingSpanMeters] at hkinematics
  rw [_data.womanMassKilograms, _data.canoeMassKilograms] at hbalance
  have hcanoe :
      displacementInMeters setup.canoeGroundDisplacement = -(9 / 7) := by
    norm_num at hkinematics hbalance ⊢
    linarith
  refine ⟨hcanoe, ?_, ?_, ?_⟩
  · norm_num [canoeTravelDistanceInMeters, hcanoe, abs_of_nonneg]
  · norm_num [AgreesWithDisplayedHundredth, canoeTravelDistanceInMeters,
      hcanoe, displayedDistanceInMeters, abs_of_nonneg, abs_of_nonpos]
  · intro other hother
    cases other with
    | A =>
        norm_num [displayedDistanceInMeters, canoeTravelDistanceInMeters,
          hcanoe, abs_of_nonneg, abs_of_nonpos]
    | B => exact (hother rfl).elim
    | C =>
        norm_num [displayedDistanceInMeters, canoeTravelDistanceInMeters,
          hcanoe, abs_of_nonneg, abs_of_nonpos]
    | D =>
        norm_num [displayedDistanceInMeters, canoeTravelDistanceInMeters,
          hcanoe, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0769
