import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0707

open Dimension

/-!
# Static forces on a simplified forearm

The primary image shows a horizontal forearm pivoted at the elbow.  A tendon
force acts upward at a point `4.0 cm` from the elbow, a `450 N` barbell force
acts downward `35 cm` from the elbow, and the upper arm exerts a downward
reaction at the elbow.

Positions and forces are unit-independent Physlib quantities.  Real-valued
coordinates, magnitudes, and torques below are explicitly coherent-SI
readouts in metres, newtons, and newton-metres.

There is a source-level mismatch worth retaining in the formal statement:
the prose asks for the elbow-force magnitude, whereas the image says “Find
`F_tendon`”, and the recorded choice `C: 3900 N` is the nearest offered value
to the tendon force.  Force and torque equilibrium instead make choice `D`
the nearest offered value to the elbow reaction.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L² T⁻²` of torque. -/
def torqueDimension : Dimension :=
  L𝓭 * forceDimension

/-- A unit-independent nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent signed position vector in the figure's plane. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful
    (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent physical force vector in the figure's plane. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- The dimensionful type occupied by a signed planar torque component. -/
abbrev PlanarTorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- Coordinate `0`, the horizontal axis pointing right in the figure. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, the vertical axis pointing up in the figure. -/
def yAxis : Fin 2 := 1

/-- Coherent-SI metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the two distance labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI position-vector readout, with coordinates in metres. -/
def positionInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Coherent-SI force-vector readout, with coordinates in newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- Euclidean magnitude, in newtons, of a physical planar force. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/--
The out-of-plane component of `(applicationPoint - pivot) × force`, read in
newton-metres.  Its sign is positive for counterclockwise torque in the
figure's right-handed coordinate convention.
-/
def planarTorqueInNewtonMeters
    (pivot applicationPoint : PlanarPositionQuantity)
    (force : PlanarForceQuantity) : ℝ :=
  let leverArm :=
    positionInMeters applicationPoint - positionInMeters pivot
  leverArm xAxis * forceVectorInNewtons force yAxis -
    leverArm yAxis * forceVectorInNewtons force xAxis

/-! ## Named figure content and physical setup -/

/-- The three force arrows named in the problem and primary image. -/
inductive AppliedForceLabel where
  | tendon
  | elbowReaction
  | barbell
  deriving DecidableEq, Fintype, Repr

/-- Distinguished force-application locations along the forearm. -/
inductive ApplicationPointLabel where
  | elbowJoint
  | tendonAttachment
  | barbellEnd
  deriving DecidableEq, Fintype, Repr

/-- Rigid-body elements visibly represented in the primary image. -/
inductive FigureElement where
  | upperArm
  | forearm
  | elbowJoint
  deriving DecidableEq, Fintype, Repr

/-- Literal physical-quantity labels printed in the supplied raster. -/
inductive FigureQuantityLabel where
  | forceTendon
  | forceElbow
  | forceBarbell
  | distanceTendon
  | distanceArm
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions used by the three force arrows. -/
inductive ArrowDirection where
  | up
  | down
  deriving DecidableEq, Repr

/-- The direction visibly assigned to each force arrow. -/
def expectedArrowDirection : AppliedForceLabel → ArrowDirection
  | .tendon => .up
  | .elbowReaction => .down
  | .barbell => .down

/-- The application point visibly assigned to each force arrow. -/
def expectedApplicationPoint : AppliedForceLabel → ApplicationPointLabel
  | .tendon => .tendonAttachment
  | .elbowReaction => .elbowJoint
  | .barbell => .barbellEnd

/-- Qualitative and literal content transcribed from image `707.png`. -/
structure ForearmStaticsFigure where
  showsElement : FigureElement → Bool
  showsForceArrow : AppliedForceLabel → Bool
  showsQuantityLabel : FigureQuantityLabel → Bool
  arrowDirection : AppliedForceLabel → ArrowDirection
  arrowApplicationPoint : AppliedForceLabel → ApplicationPointLabel
  upperArmDrawnVertical : Bool
  forearmDrawnHorizontal : Bool
  tendonAttachmentBetweenElbowAndBarbellEnd : Bool
  showsTorqueArcAboutElbow : Bool
  showsKnownDataBlock : Bool
  showsFindTendonForceBlock : Bool

/--
Independent quantities in the simplified forearm experiment.  No requested
force magnitude or answer choice is defined into this setup.
-/
structure ForearmStaticsSetup where
  figure : ForearmStaticsFigure
  elbowPosition : PlanarPositionQuantity
  tendonPosition : PlanarPositionQuantity
  barbellPosition : PlanarPositionQuantity
  tendonDistanceFromElbow : LengthQuantity
  armDistanceFromElbow : LengthQuantity
  appliedForce : AppliedForceLabel → PlanarForceQuantity

/-! ## Figure evidence, numerical data, geometry, and governing laws -/

/--
Primary-image evidence: the two arm segments, all five quantity labels, all
three arrows and their application points, and the torque annotation.
-/
structure MatchesSuppliedFigure (setup : ForearmStaticsSetup) : Prop where
  everyArmElementShown :
    ∀ element, setup.figure.showsElement element = true
  everyForceArrowShown :
    ∀ label, setup.figure.showsForceArrow label = true
  everyQuantityLabelShown :
    ∀ label, setup.figure.showsQuantityLabel label = true
  displayedArrowDirections :
    ∀ label,
      setup.figure.arrowDirection label = expectedArrowDirection label
  displayedApplicationPoints :
    ∀ label,
      setup.figure.arrowApplicationPoint label =
        expectedApplicationPoint label
  upperArmIsVertical : setup.figure.upperArmDrawnVertical = true
  forearmIsHorizontal : setup.figure.forearmDrawnHorizontal = true
  tendonLiesBetweenElbowAndBarbell :
    setup.figure.tendonAttachmentBetweenElbowAndBarbellEnd = true
  torqueArcShown : setup.figure.showsTorqueArcAboutElbow = true
  knownDataBlockShown : setup.figure.showsKnownDataBlock = true
  figureAsksForTendonForce :
    setup.figure.showsFindTendonForceBlock = true

/--
The three numerical values printed in the figure.  Neither the tendon-force
magnitude nor the elbow-force magnitude occurs among these source readouts.
-/
structure MatchesProblemReadouts (setup : ForearmStaticsSetup) : Prop where
  tendonDistanceCentimeters :
    lengthInCentimeters setup.tendonDistanceFromElbow = 4.0
  armDistanceCentimeters :
    lengthInCentimeters setup.armDistanceFromElbow = 35
  barbellForceNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .barbell) = 450

/--
Coordinate realization of the horizontal forearm: the elbow is the origin,
and both force application points lie to its right on the horizontal axis at
the two named physical distances.
-/
structure MatchesForearmGeometry (setup : ForearmStaticsSetup) : Prop where
  elbowAtOrigin :
    positionInMeters setup.elbowPosition = 0
  tendonOnHorizontalForearm :
    positionInMeters setup.tendonPosition yAxis = 0
  barbellOnHorizontalForearm :
    positionInMeters setup.barbellPosition yAxis = 0
  tendonLeverArmMeters :
    positionInMeters setup.tendonPosition xAxis -
        positionInMeters setup.elbowPosition xAxis =
      lengthInMeters setup.tendonDistanceFromElbow
  barbellLeverArmMeters :
    positionInMeters setup.barbellPosition xAxis -
        positionInMeters setup.elbowPosition xAxis =
      lengthInMeters setup.armDistanceFromElbow
  tendonStrictlyBetweenElbowAndBarbell :
    0 < lengthInMeters setup.tendonDistanceFromElbow ∧
      lengthInMeters setup.tendonDistanceFromElbow <
        lengthInMeters setup.armDistanceFromElbow

/--
The force directions shown in the image, expressed as coherent-SI Cartesian
components.  These equations state only directions; no unknown force value is
inserted.
-/
structure MatchesDisplayedForceDirections
    (setup : ForearmStaticsSetup) : Prop where
  everyForceIsVertical :
    ∀ label, forceVectorInNewtons (setup.appliedForce label) xAxis = 0
  tendonPointsUp :
    forceVectorInNewtons (setup.appliedForce .tendon) yAxis =
      forceMagnitudeInNewtons (setup.appliedForce .tendon)
  elbowReactionPointsDown :
    forceVectorInNewtons (setup.appliedForce .elbowReaction) yAxis =
      -forceMagnitudeInNewtons (setup.appliedForce .elbowReaction)
  barbellForcePointsDown :
    forceVectorInNewtons (setup.appliedForce .barbell) yAxis =
      -forceMagnitudeInNewtons (setup.appliedForce .barbell)

/--
Static translational and rotational equilibrium of the forearm.  This is the
governing physical law and contains neither requested numerical magnitude nor
an answer-choice label.
-/
structure SatisfiesForearmStaticEquilibrium
    (setup : ForearmStaticsSetup) : Prop where
  netForceIsZero :
    forceVectorInNewtons (setup.appliedForce .tendon) +
        forceVectorInNewtons (setup.appliedForce .elbowReaction) +
        forceVectorInNewtons (setup.appliedForce .barbell) =
      0
  netTorqueAboutElbowIsZero :
    planarTorqueInNewtonMeters
          setup.elbowPosition setup.tendonPosition
          (setup.appliedForce .tendon) +
        planarTorqueInNewtonMeters
          setup.elbowPosition setup.elbowPosition
          (setup.appliedForce .elbowReaction) +
        planarTorqueInNewtonMeters
          setup.elbowPosition setup.barbellPosition
          (setup.appliedForce .barbell) =
      0

/-! ## Displayed answers and current conclusions -/

/-- The four answer labels supplied with the prose question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force magnitude in newtons printed beside each answer label. -/
def displayedForceInNewtons : AnswerChoice → ℝ
  | .A => 3800
  | .B => 4000
  | .C => 3900
  | .D => 3700

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A choice is at least as close to a force magnitude as every alternative. -/
def IsNearestDisplayedForce
    (force : PlanarForceQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |forceMagnitudeInNewtons force - displayedForceInNewtons choice| ≤
      |forceMagnitudeInNewtons force - displayedForceInNewtons other|

/-- A choice is the unique nearest displayed force magnitude. -/
def IsUniqueNearestDisplayedForce
    (force : PlanarForceQuantity) (choice : AnswerChoice) : Prop :=
  IsNearestDisplayedForce force choice ∧
    ∀ other : AnswerChoice,
      IsNearestDisplayedForce force other → other = choice

/--
Torque balance gives a tendon force of `3937.5 N`.  Vertical force balance
then gives a downward elbow reaction of `3487.5 N`.  Consequently the
dataset's recorded choice `C: 3900 N` is the unique nearest choice for the
tendon force named in the figure's “Find” block, while `D: 3700 N` is the
unique nearest offered choice for the elbow force actually asked for in the
prose.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0707:target`.
-/
theorem problem_phyx_mini_0707
    (setup : ForearmStaticsSetup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : MatchesForearmGeometry setup)
    (hDirections : MatchesDisplayedForceDirections setup)
    (hStatics : SatisfiesForearmStaticEquilibrium setup) :
    forceMagnitudeInNewtons (setup.appliedForce .tendon) = 7875 / 2 ∧
      forceMagnitudeInNewtons (setup.appliedForce .elbowReaction) = 6975 / 2 ∧
      IsUniqueNearestDisplayedForce
        (setup.appliedForce .tendon) recordedAnswerChoice ∧
      IsUniqueNearestDisplayedForce
        (setup.appliedForce .elbowReaction) .D := by
  have hTendonDistance :
      lengthInMeters setup.tendonDistanceFromElbow = 1 / 25 := by
    have h := hReadouts.tendonDistanceCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hArmDistance :
      lengthInMeters setup.armDistanceFromElbow = 7 / 20 := by
    have h := hReadouts.armDistanceCentimeters
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hTendonX :
      positionInMeters setup.tendonPosition xAxis =
        lengthInMeters setup.tendonDistanceFromElbow := by
    have hElbowX :=
      congrArg (fun p => p xAxis) hGeometry.elbowAtOrigin
    simpa [hElbowX] using hGeometry.tendonLeverArmMeters
  have hBarbellX :
      positionInMeters setup.barbellPosition xAxis =
        lengthInMeters setup.armDistanceFromElbow := by
    have hElbowX :=
      congrArg (fun p => p xAxis) hGeometry.elbowAtOrigin
    simpa [hElbowX] using hGeometry.barbellLeverArmMeters
  have hTorque :
      lengthInMeters setup.tendonDistanceFromElbow *
          forceMagnitudeInNewtons (setup.appliedForce .tendon) +
        -(lengthInMeters setup.armDistanceFromElbow *
          forceMagnitudeInNewtons (setup.appliedForce .barbell)) = 0 := by
    simpa [planarTorqueInNewtonMeters, hGeometry.elbowAtOrigin,
      hGeometry.tendonOnHorizontalForearm,
      hGeometry.barbellOnHorizontalForearm, hTendonX, hBarbellX,
      hDirections.everyForceIsVertical, hDirections.tendonPointsUp,
      hDirections.barbellForcePointsDown] using
        hStatics.netTorqueAboutElbowIsZero
  rw [hTendonDistance, hArmDistance,
    hReadouts.barbellForceNewtons] at hTorque
  have hTendonMagnitude :
      forceMagnitudeInNewtons (setup.appliedForce .tendon) = 7875 / 2 := by
    norm_num at hTorque ⊢
    linarith
  have hForceY :
      forceMagnitudeInNewtons (setup.appliedForce .tendon) +
          -forceMagnitudeInNewtons (setup.appliedForce .elbowReaction) +
        -forceMagnitudeInNewtons (setup.appliedForce .barbell) = 0 := by
    have h :=
      congrArg (fun force => force yAxis) hStatics.netForceIsZero
    simpa [hDirections.tendonPointsUp,
      hDirections.elbowReactionPointsDown,
      hDirections.barbellForcePointsDown] using h
  have hElbowMagnitude :
      forceMagnitudeInNewtons (setup.appliedForce .elbowReaction) =
        6975 / 2 := by
    rw [hTendonMagnitude, hReadouts.barbellForceNewtons] at hForceY
    norm_num at hForceY ⊢
    linarith
  refine ⟨hTendonMagnitude, hElbowMagnitude, ?_, ?_⟩
  · constructor
    · intro other
      fin_cases other <;>
        norm_num [IsNearestDisplayedForce, recordedAnswerChoice,
          displayedForceInNewtons, hTendonMagnitude]
    · intro other hNearest
      fin_cases other
      · have h := hNearest .C
        norm_num [IsNearestDisplayedForce, displayedForceInNewtons,
          hTendonMagnitude] at h
      · have h := hNearest .C
        norm_num [IsNearestDisplayedForce, displayedForceInNewtons,
          hTendonMagnitude] at h
      · rfl
      · have h := hNearest .C
        norm_num [IsNearestDisplayedForce, displayedForceInNewtons,
          hTendonMagnitude] at h
  · constructor
    · intro other
      fin_cases other <;>
        norm_num [IsNearestDisplayedForce, displayedForceInNewtons,
          hElbowMagnitude]
    · intro other hNearest
      fin_cases other
      · have h := hNearest .D
        norm_num [IsNearestDisplayedForce, displayedForceInNewtons,
          hElbowMagnitude] at h
      · have h := hNearest .D
        norm_num [IsNearestDisplayedForce, displayedForceInNewtons,
          hElbowMagnitude] at h
      · have h := hNearest .D
        norm_num [IsNearestDisplayedForce, displayedForceInNewtons,
          hElbowMagnitude] at h
      · rfl

end PhyXMiniProblems.ProblemPhyXMini0707
