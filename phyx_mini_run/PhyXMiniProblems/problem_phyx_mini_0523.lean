import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0523

open Dimension

/-!
# Baseball thrown backward from a moving truck

The supplied image fixes a horizontal one-dimensional axis.  Rightward is
positive: the truck moves right relative to the ground, while the baseball is
thrown left relative to the truck.  The observer shown on the ground measures
the baseball in the ground frame.

Velocities are unit-independent, signed physical quantities with dimension
`length / time`.  Real numbers appear only as readouts in explicitly selected
length and time units and as the displayed multiple-choice values.
-/

/-! ## Dimensionful velocity and unit readouts -/

/-- A signed one-dimensional physical velocity, independent of unit choice. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a signed velocity in coherent selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a signed velocity in metres per second. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-! ## Frames, participants, and labels in the primary figure -/

/-- The two inertial frames used in the relative-motion calculation. -/
inductive InertialFrameLabel where
  | ground
  | truck
  deriving DecidableEq, Repr

/-- Directions along the horizontal axis of the supplied image. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The two velocity arrows drawn in the supplied image. -/
inductive FigureVelocityArrow where
  | baseball
  | truck
  deriving DecidableEq, Repr

/-- The mathematical labels printed above the two velocity arrows. -/
inductive PrintedVelocityLabel where
  | v
  | vTruck
  deriving DecidableEq, Repr

/-- Named physical features visible in `phyx_data/test_image/523.png`. -/
inductive FigureFeature where
  | pickupTruck
  | personInTruckBed
  | baseball
  | observerOnGround
  | groundSurface
  deriving DecidableEq, Fintype, Repr

/-- Qualitative data carried by the primary figure. -/
structure TruckBaseballFigure where
  shows : FigureFeature → Bool
  arrowDirection : FigureVelocityArrow → HorizontalDirection
  arrowLabel : FigureVelocityArrow → PrintedVelocityLabel

/-!
Independent physical quantities in the scenario.  In particular,
`baseballVelocityRelativeGround` is an observable field; it is not defined by
the requested answer or by the Galilean addition law.
-/
structure TruckBaseballRelativeMotionSetup where
  figure : TruckBaseballFigure
  positiveAxisDirection : HorizontalDirection
  throwerFrame : InertialFrameLabel
  observerMeasurementFrame : InertialFrameLabel
  truckVelocityRelativeGround : SignedVelocityQuantity
  baseballVelocityRelativeTruck : SignedVelocityQuantity
  baseballVelocityRelativeGround : SignedVelocityQuantity

/-! ## Scenario, figure/data readouts, and governing physics -/

/-- Frame assignments and sign convention stated or implied by the problem. -/
structure MatchesTruckBaseballScenario
    (setup : TruckBaseballRelativeMotionSetup) : Prop where
  rightwardIsPositive : setup.positiveAxisDirection = .right
  throwerUsesTruckFrame : setup.throwerFrame = .truck
  observerUsesGroundFrame : setup.observerMeasurementFrame = .ground

/-!
Evidence transcribed from the primary image: truck and thrower, baseball,
ground observer, and ground are visible; the arrow labelled `v` points left,
whereas the arrow labelled `v_truck` points right.
-/
structure MatchesSuppliedTruckBaseballFigure
    (figure : TruckBaseballFigure) : Prop where
  everyNamedFeatureShown : ∀ feature, figure.shows feature = true
  baseballArrowLabelIsV : figure.arrowLabel .baseball = .v
  truckArrowLabelIsVTruck : figure.arrowLabel .truck = .vTruck
  baseballArrowPointsLeft : figure.arrowDirection .baseball = .left
  truckArrowPointsRight : figure.arrowDirection .truck = .right

/-!
Numerical velocity readouts stated in the prose, using the figure's convention
that rightward is positive.  The truck has velocity `+10 m/s` relative to the
ground, and the backward-thrown ball has velocity `-20 m/s` relative to the
truck.  No ground-frame baseball velocity occurs here.
-/
structure MatchesProblemVelocityReadouts
    (setup : TruckBaseballRelativeMotionSetup) : Prop where
  truckRelativeGroundMetersPerSecond :
    velocityInMetersPerSecond setup.truckVelocityRelativeGround = 10
  baseballRelativeTruckMetersPerSecond :
    velocityInMetersPerSecond setup.baseballVelocityRelativeTruck = -20

/-!
The one-dimensional Galilean velocity-composition law
`v_ball,ground = v_ball,truck + v_truck,ground`, required in every coherent
choice of length and time units.  This is a governing law and does not assign
the current problem's numerical answer to the ground-frame baseball velocity.
-/
structure SatisfiesGalileanVelocityComposition
    (setup : TruckBaseballRelativeMotionSetup) : Prop where
  velocityAddition : ∀ lengthUnit timeUnit,
    velocityReadout lengthUnit timeUnit
        setup.baseballVelocityRelativeGround =
      velocityReadout lengthUnit timeUnit
          setup.baseballVelocityRelativeTruck +
        velocityReadout lengthUnit timeUnit
          setup.truckVelocityRelativeGround

/-! ## Displayed answer data and target -/

/-- Labels of the four multiple-choice answers in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Signed velocity printed beside each answer choice, in metres per second. -/
def displayedVelocityInMetersPerSecond : AnswerChoice → ℝ
  | .A => 30
  | .B => 20
  | .C => -30
  | .D => -10

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The ground observer's baseball-velocity readout agrees with a choice. -/
def MatchesAnswerChoice
    (setup : TruckBaseballRelativeMotionSetup)
    (choice : AnswerChoice) : Prop :=
  velocityInMetersPerSecond setup.baseballVelocityRelativeGround =
    displayedVelocityInMetersPerSecond choice

/-!
Galilean addition gives `-20 + 10 = -10 m/s`: the ball moves left at
`10 m/s` in the ground frame, so the displayed answer is D.

This formalizes `thm:physics:phyx_mini_0523:target`.
-/
theorem problem_phyx_mini_0523
    (setup : TruckBaseballRelativeMotionSetup)
    (_scenario : MatchesTruckBaseballScenario setup)
    (_figure : MatchesSuppliedTruckBaseballFigure setup.figure)
    (_readouts : MatchesProblemVelocityReadouts setup)
    (_laws : SatisfiesGalileanVelocityComposition setup) :
    velocityInMetersPerSecond setup.baseballVelocityRelativeGround = -10 ∧
      MatchesAnswerChoice setup recordedDatasetAnswer := by
  have hGround :
      velocityInMetersPerSecond setup.baseballVelocityRelativeGround = -10 := by
    have h := _laws.velocityAddition LengthUnit.meters TimeUnit.seconds
    change velocityInMetersPerSecond setup.baseballVelocityRelativeGround =
      velocityInMetersPerSecond setup.baseballVelocityRelativeTruck +
        velocityInMetersPerSecond setup.truckVelocityRelativeGround at h
    rw [_readouts.baseballRelativeTruckMetersPerSecond,
      _readouts.truckRelativeGroundMetersPerSecond] at h
    norm_num at h ⊢
    exact h
  constructor
  · exact hGround
  · simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      displayedVelocityInMetersPerSecond] using hGround

end PhyXMiniProblems.ProblemPhyXMini0523
