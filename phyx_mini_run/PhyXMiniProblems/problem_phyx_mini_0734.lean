import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Direction of the displacement to point A in a branching ant trail

The supplied diagram is an outward-oriented binary tree of straight chemical
trail sections.  Every section has length `2.0 cm`; at every branch the two
outward continuations are obtained by turns of `30°` left and right, hence are
separated by `60°`.  Section `v` is parallel to the displayed `y` axis and
points in its positive direction.

Physical points are assigned unit-independent planar positions of dimension
length.  Complex numbers occur only as coordinate readouts in a selected
length unit.  Multiplication by a point of the complex unit circle represents
the dimensionless rotation of a displacement readout.

Assumption/target boundary:

* `MatchesAntTrailFigure` records labels, endpoints, branch incidence, the
  `2 cm` calibration, and the orientation of section `v` read from the image;
* `SymmetricTrailBranchingLaws` records the general `±30°` turn law at each
  displayed bifurcation;
* there are no previous-part results;
* the conclusion that the nest-to-`A` displacement has angle `90°` occurs only
  in `ant_displacement_from_nest_to_A_has_angle_ninety_degrees`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0734

open Dimension

/-! ## Dimensionful planar positions and coordinate readouts -/

/-- A unit-independent planar position carrying physical dimension length. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℂ)

/-- Complex Cartesian coordinates of a physical position in a selected length unit. -/
def positionReadout
    (unit : LengthUnit) (position : PlanarPositionQuantity) : ℂ :=
  (position ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-! ## Labels and primary-image geometry -/

/-- All straight-section labels visible in the primary image, including `u`, `v`, and `w`. -/
inductive TrailSectionLabel where
  | a | b | c | d | e | f | g | h | i | j | k | l
  | m | n | o | p | q | r | s | t | u | v | w
  deriving DecidableEq, Fintype, Repr

/-- The two dark, lettered entry points visible in the primary image. -/
inductive EntryPointLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Multiple-choice labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The angle, in degrees, printed next to each answer choice. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 60
  | .B => 75
  | .C => 90
  | .D => 120

/-!
An abstract combinatorial diagram together with physical vertex positions.
The start and end of every section are oriented away from the nest.  This
orientation makes the prose statement about two outward choices and one
inward choice precise once the branch incidences below are supplied.
-/
structure AntTrailDiagram where
  Vertex : Type
  nest : Vertex
  entryPoint : EntryPointLabel → Vertex
  sectionStartTowardNest : TrailSectionLabel → Vertex
  sectionEndAwayFromNest : TrailSectionLabel → Vertex
  vertexPosition : Vertex → PlanarPositionQuantity
  sectionLabelShown : TrailSectionLabel → Bool
  entryPointShown : EntryPointLabel → Bool
  positiveXAxisShown : Bool
  positiveYAxisShown : Bool

/-- Outward displacement vector of a trail section, read in a selected unit. -/
def sectionDisplacementReadout
    (unit : LengthUnit) (diagram : AntTrailDiagram)
    (edge : TrailSectionLabel) : ℂ :=
  positionReadout unit
      (diagram.vertexPosition (diagram.sectionEndAwayFromNest edge)) -
    positionReadout unit
      (diagram.vertexPosition (diagram.sectionStartTowardNest edge))

/-- Outward displacement vector of a section in the centimeter calibration of the figure. -/
def sectionDisplacementCentimeters
    (diagram : AntTrailDiagram) (edge : TrailSectionLabel) : ℂ :=
  sectionDisplacementReadout LengthUnit.centimeters diagram edge

/-- Physical displacement from the nest to an indicated entry point, in centimeters. -/
def displacementFromNestCentimeters
    (diagram : AntTrailDiagram) (entry : EntryPointLabel) : ℂ :=
  positionReadout LengthUnit.centimeters
      (diagram.vertexPosition (diagram.entryPoint entry)) -
    positionReadout LengthUnit.centimeters
      (diagram.vertexPosition diagram.nest)

/-- Principal direction angle, in radians, relative to the positive `x` axis. -/
def displacementDirectionRadians
    (diagram : AntTrailDiagram) (entry : EntryPointLabel) : ℝ :=
  Complex.arg (displacementFromNestCentimeters diagram entry)

/-! ## Branch incidence and calibrated figure readouts -/

/--
The outward end of `incoming` is the common outward start of the two child
sections.  Thus an ant moving away from the nest has two continuations, while
one moving toward the nest has the unique parent section.
-/
def SectionsFormBifurcation
    (diagram : AntTrailDiagram)
    (incoming leftChild rightChild : TrailSectionLabel) : Prop :=
  diagram.sectionEndAwayFromNest incoming =
      diagram.sectionStartTowardNest leftChild ∧
    diagram.sectionEndAwayFromNest incoming =
      diagram.sectionStartTowardNest rightChild

/-!
Primary-image and prose readouts.  The eleven incidence fields transcribe the
entire displayed tree with mathematical positive (counterclockwise) turns
listed first.  In particular, the nest-to-`A` route is `w`, `v`, `i`, `h`;
that route is figure topology, not the requested displacement angle.
-/
structure MatchesAntTrailFigure (diagram : AntTrailDiagram) : Prop where
  everySectionLabelShown :
    ∀ edge, diagram.sectionLabelShown edge = true
  bothEntryPointsShown :
    ∀ entry, diagram.entryPointShown entry = true
  positiveXAxisIsShown : diagram.positiveXAxisShown = true
  positiveYAxisIsShown : diagram.positiveYAxisShown = true
  sectionWStartsAtNest :
    diagram.sectionStartTowardNest .w = diagram.nest
  pointAIsEndOfSectionH :
    diagram.sectionEndAwayFromNest .h = diagram.entryPoint .A
  pointBIsEndOfSectionO :
    diagram.sectionEndAwayFromNest .o = diagram.entryPoint .B
  branchWToVAndU : SectionsFormBifurcation diagram .w .v .u
  branchVToIAndJ : SectionsFormBifurcation diagram .v .i .j
  branchIToGAndH : SectionsFormBifurcation diagram .i .g .h
  branchGToDAndC : SectionsFormBifurcation diagram .g .d .c
  branchCToAAndB : SectionsFormBifurcation diagram .c .a .b
  branchDToFAndE : SectionsFormBifurcation diagram .d .f .e
  branchJToKAndP : SectionsFormBifurcation diagram .j .k .p
  branchKToMAndL : SectionsFormBifurcation diagram .k .m .l
  branchPToNAndO : SectionsFormBifurcation diagram .p .n .o
  branchUToSAndT : SectionsFormBifurcation diagram .u .s .t
  branchSToRAndQ : SectionsFormBifurcation diagram .s .r .q
  everySectionHasLengthTwoCentimeters :
    ∀ edge, ‖sectionDisplacementCentimeters diagram edge‖ = 2
  sectionVIsParallelToYAxis :
    (sectionDisplacementCentimeters diagram .v).re = 0
  sectionVPointsInPositiveYDirection :
    0 < (sectionDisplacementCentimeters diagram .v).im

/-! ## Symmetric-bifurcation law -/

/-- Rotate a planar displacement counterclockwise by a radian angle. -/
def rotateByRadians (angle : ℝ) (displacement : ℂ) : ℂ :=
  ((((angle : Real.Angle).toCircle : Circle) : ℂ) * displacement)

/-- A small `30°` left turn in the ant's outward travel direction. -/
def turnThirtyDegreesLeft (displacement : ℂ) : ℂ :=
  rotateByRadians (Real.pi / 6) displacement

/-- A small `30°` right turn in the ant's outward travel direction. -/
def turnThirtyDegreesRight (displacement : ℂ) : ℂ :=
  rotateByRadians (-(Real.pi / 6)) displacement

/--
The two child displacement vectors at one symmetric bifurcation.  They are
obtained by `+30°` and `-30°` rotations of the incoming outward direction, so
the angle separating them is `60°`.
-/
def IsSymmetricSixtyDegreeBifurcation
    (diagram : AntTrailDiagram)
    (incoming leftChild rightChild : TrailSectionLabel) : Prop :=
  sectionDisplacementCentimeters diagram leftChild =
      turnThirtyDegreesLeft
        (sectionDisplacementCentimeters diagram incoming) ∧
    sectionDisplacementCentimeters diagram rightChild =
      turnThirtyDegreesRight
        (sectionDisplacementCentimeters diagram incoming)

/-!
The common symmetric `60°` branching rule instantiated at every bifurcation
drawn in the primary image.  None of these fields states or encodes the net
direction from the nest to point `A`.
-/
structure SymmetricTrailBranchingLaws
    (diagram : AntTrailDiagram) : Prop where
  atW : IsSymmetricSixtyDegreeBifurcation diagram .w .v .u
  atV : IsSymmetricSixtyDegreeBifurcation diagram .v .i .j
  atI : IsSymmetricSixtyDegreeBifurcation diagram .i .g .h
  atG : IsSymmetricSixtyDegreeBifurcation diagram .g .d .c
  atC : IsSymmetricSixtyDegreeBifurcation diagram .c .a .b
  atD : IsSymmetricSixtyDegreeBifurcation diagram .d .f .e
  atJ : IsSymmetricSixtyDegreeBifurcation diagram .j .k .p
  atK : IsSymmetricSixtyDegreeBifurcation diagram .k .m .l
  atP : IsSymmetricSixtyDegreeBifurcation diagram .p .n .o
  atU : IsSymmetricSixtyDegreeBifurcation diagram .u .s .t
  atS : IsSymmetricSixtyDegreeBifurcation diagram .s .r .q

/-! ## Requested displacement direction -/

/--
An ant entering at point `A` is displaced from the nest in the positive
`y` direction.  Consequently its angle relative to the positive `x` axis is
`π / 2` radians, i.e. `90°`, which is answer choice `C`.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0734:target`.
-/
theorem ant_displacement_from_nest_to_A_has_angle_ninety_degrees
    (diagram : AntTrailDiagram)
    (figureData : MatchesAntTrailFigure diagram)
    (branchingLaws : SymmetricTrailBranchingLaws diagram) :
    displacementDirectionRadians diagram .A = Real.pi / 2 := by
  rcases figureData.branchWToVAndU with ⟨hWVincidence, _⟩
  rcases figureData.branchVToIAndJ with ⟨hVIincidence, _⟩
  rcases figureData.branchIToGAndH with ⟨_, hIHincidence⟩
  have hroute :
      displacementFromNestCentimeters diagram .A =
        sectionDisplacementCentimeters diagram .w +
          sectionDisplacementCentimeters diagram .v +
          sectionDisplacementCentimeters diagram .i +
          sectionDisplacementCentimeters diagram .h := by
    unfold displacementFromNestCentimeters sectionDisplacementCentimeters
      sectionDisplacementReadout
    rw [← figureData.pointAIsEndOfSectionH,
      ← figureData.sectionWStartsAtNest, hWVincidence, hVIincidence,
      hIHincidence]
    ring
  rcases branchingLaws.atW with ⟨hWVturn, _⟩
  rcases branchingLaws.atV with ⟨hVIturn, _⟩
  rcases branchingLaws.atI with ⟨_, hIHturn⟩
  have hWturn :
      sectionDisplacementCentimeters diagram .w =
        turnThirtyDegreesRight
          (sectionDisplacementCentimeters diagram .v) := by
    rw [hWVturn]
    simp [turnThirtyDegreesRight, turnThirtyDegreesLeft, rotateByRadians]
  have hHturn :
      sectionDisplacementCentimeters diagram .h =
        sectionDisplacementCentimeters diagram .v := by
    rw [hIHturn, hVIturn]
    simp [turnThirtyDegreesRight, turnThirtyDegreesLeft, rotateByRadians]
  have hrotate (angle : ℝ) (z : ℂ) :
      rotateByRadians angle z =
        (Real.cos angle + Real.sin angle * Complex.I) * z := by
    unfold rotateByRadians
    rw [Real.Angle.coe_toCircle]
    rfl
  apply Complex.arg_eq_pi_div_two_iff.mpr
  rw [hroute, hWturn, hVIturn, hHturn]
  constructor
  · rw [turnThirtyDegreesRight, turnThirtyDegreesLeft, hrotate, hrotate]
    simp [Real.cos_pi_div_six, Real.sin_pi_div_six,
      figureData.sectionVIsParallelToYAxis]
  · rw [turnThirtyDegreesRight, turnThirtyDegreesLeft, hrotate, hrotate]
    simp [Real.cos_pi_div_six, Real.sin_pi_div_six,
      figureData.sectionVIsParallelToYAxis]
    have hVim :
        0 < (sectionDisplacementCentimeters diagram .v).im :=
      figureData.sectionVPointsInPositiveYDirection
    positivity

end PhyXMiniProblems.ProblemPhyXMini0734
