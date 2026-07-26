import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Projection
import Physlib.Units.WithDim.Basic

/-!
# First sight of a burglar in a corridor mirror

This file formalizes the textual plane-mirror problem in `phyx_mini_0162`.
The supplied bitmap is inconsistent with that text: it depicts a plano-convex
lens with labels `n = 1.50`, `s = 8.0 mm`, and `s' = 160 mm`, not the corridor
containing the plane mirror `M`, burglar `B`, and guard `S`.  Consequently the
three corridor spans labelled `d` are retained as abstract Euclidean landmark
distances rather than assigned unsupported coordinates.

Coordinates are scalar readouts in SI metres.  Physical distances and the
figure parameter `d` use Physlib's dimension-carrying quantity type.  The
finite reflecting part of the mirror is distinguished from its complete
affine carrier, which is used by the method of virtual images.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0162

open Dimension CarriesDimension UnitChoices

/-- Positions in the overhead two-dimensional corridor diagram. -/
abbrev OpticalPlane := EuclideanSpace ℝ (Fin 2)

/-- A genuine physical quantity with the dimension of length. -/
abbrev LengthQuantity := Dimensionful (WithDim L𝓭 ℝ)

/-- Convert an SI-metre readout into a dimensionful physical length. -/
noncomputable def metres (value : ℝ) : LengthQuantity :=
  toDimensionful SI ⟨value⟩

/-- Read a dimensionful length as a real number of SI metres. -/
noncomputable def lengthInMetres (length : LengthQuantity) : ℝ :=
  (length SI).val

/-- Physical distance between two points whose coordinates are metre readouts. -/
noncomputable def physicalDistance
    (first second : OpticalPlane) : LengthQuantity :=
  metres (dist first second)

/--
The finite plane mirror marked `M` in the corridor.

The complete affine line `carrier` supports Mathlib's reflection operation;
`reflectingSegment` is the part on which a physical light ray may strike.
-/
structure FinitePlaneMirror where
  carrier : AffineSubspace ℝ OpticalPlane
  carrierNonempty : Nonempty carrier
  reflectingSegment : Set OpticalPlane
  center : OpticalPlane
  center_mem_segment : center ∈ reflectingSegment
  segment_on_carrier : reflectingSegment ⊆ (carrier : Set OpticalPlane)
  carrier_is_line : Module.finrank ℝ carrier.direction = 1

namespace FinitePlaneMirror

/-- The virtual image of a point formed by reflection in the mirror carrier. -/
noncomputable def reflectPoint
    (mirror : FinitePlaneMirror) (point : OpticalPlane) : OpticalPlane :=
  letI : Nonempty mirror.carrier := mirror.carrierNonempty
  EuclideanGeometry.reflection mirror.carrier point

end FinitePlaneMirror

/--
All physical objects and named landmarks in the overhead corridor model.

`burglarPositionAt distance` is the position labelled `B` when her distance
from the mirror is `distance`.  The remaining four landmarks retain the two
horizontal and one vertical spans labelled `d` in the source description.
No field fixes the requested first-visible distance.
-/
structure CorridorMirrorSetup where
  mirrorM : FinitePlaneMirror
  guardPositionS : OpticalPlane
  burglarPositionAt : LengthQuantity → OpticalPlane
  corridorRegion : Set OpticalPlane
  leftHorizontalLandmark : OpticalPlane
  middleHorizontalLandmark : OpticalPlane
  rightHorizontalLandmark : OpticalPlane
  verticalEndLandmark : OpticalPlane
  d : LengthQuantity
  approachDirection : OpticalPlane
  guardCanSeeBurglarAt : LengthQuantity → Prop

/--
The labels and qualitative placement supplied by the corridor description.

The burglar moves on a straight line directly toward the mirror center, and
the parameter of that path is her physical distance from the center.  The
three displayed corridor spans are all the dimensionful length `d`.  No
visibility threshold or answer value is included here.
-/
structure MatchesCorridorFigure (setup : CorridorMirrorSetup) : Prop where
  d_readout : lengthInMetres setup.d = 3
  d_positive : 0 < lengthInMetres setup.d
  first_horizontal_span :
    physicalDistance setup.leftHorizontalLandmark
        setup.middleHorizontalLandmark = setup.d
  second_horizontal_span :
    physicalDistance setup.middleHorizontalLandmark
        setup.rightHorizontalLandmark = setup.d
  vertical_span :
    physicalDistance setup.rightHorizontalLandmark
        setup.verticalEndLandmark = setup.d
  guard_at_vertical_end :
    setup.guardPositionS = setup.verticalEndLandmark
  mirror_center_on_left_horizontal_section :
    setup.mirrorM.center ∈
      segment ℝ setup.leftHorizontalLandmark setup.middleHorizontalLandmark
  approach_direction_is_unit : ‖setup.approachDirection‖ = 1
  burglar_moves_directly_toward_M :
    ∀ distance : LengthQuantity,
      0 ≤ lengthInMetres distance →
        setup.burglarPositionAt distance =
          setup.mirrorM.center -
            lengthInMetres distance • setup.approachDirection
  burglar_distance_parameter :
    ∀ distance : LengthQuantity,
      0 ≤ lengthInMetres distance →
        physicalDistance (setup.burglarPositionAt distance)
            setup.mirrorM.center = distance
  guard_in_corridor : setup.guardPositionS ∈ setup.corridorRegion
  burglar_path_in_corridor :
    ∀ distance : LengthQuantity,
      0 ≤ lengthInMetres distance →
        setup.burglarPositionAt distance ∈ setup.corridorRegion

/--
A method-of-images ray from `S` to the virtual image of `B` meets the finite
mirror at `hit`, while both physical ray legs remain in the corridor.
-/
def HasUnobstructedImageRay
    (setup : CorridorMirrorSetup) (distance : LengthQuantity) : Prop :=
  ∃ hit : OpticalPlane,
    hit ∈ setup.mirrorM.reflectingSegment ∧
      hit ∈ segment ℝ setup.guardPositionS
        (setup.mirrorM.reflectPoint (setup.burglarPositionAt distance)) ∧
      segment ℝ setup.guardPositionS hit ⊆ setup.corridorRegion ∧
      segment ℝ (setup.burglarPositionAt distance) hit ⊆ setup.corridorRegion

/-- SI-metre readout of the first horizontal corridor span labelled `d`. -/
def nearHorizontalSpanInMetres (setup : CorridorMirrorSetup) : ℝ :=
  lengthInMetres
    (physicalDistance setup.leftHorizontalLandmark
      setup.middleHorizontalLandmark)

/-- SI-metre readout of the second horizontal corridor span labelled `d`. -/
def farHorizontalSpanInMetres (setup : CorridorMirrorSetup) : ℝ :=
  lengthInMetres
    (physicalDistance setup.middleHorizontalLandmark
      setup.rightHorizontalLandmark)

/-- SI-metre readout of the vertical corridor span labelled `d`. -/
def verticalSpanInMetres (setup : CorridorMirrorSetup) : ℝ :=
  lengthInMetres
    (physicalDistance setup.rightHorizontalLandmark
      setup.verticalEndLandmark)

/--
After unfolding the reflection in `M`, the straight sightline clears the
occluding wall edge exactly when

`x * (d_near + d_far) ≤ d_vertical * d_near`.

This is the unsolved similar-triangle condition at an arbitrary burglar
distance `x`; it neither selects the first-visible position nor states an
answer choice.
-/
def UnfoldedSightLineClearsWallEdge
    (setup : CorridorMirrorSetup) (distance : LengthQuantity) : Prop :=
  lengthInMetres distance *
      (nearHorizontalSpanInMetres setup + farHorizontalSpanInMetres setup) ≤
    verticalSpanInMetres setup * nearHorizontalSpanInMetres setup

/--
The governing finite-plane-mirror visibility law.  It combines specular
reflection via the virtual image, obstruction by the corridor walls, and the
similar-triangle clearance relation for the captioned L-shaped corridor.
Neither Mathlib nor Physlib provides this observer-visibility interface.
-/
structure ObeysFinitePlaneMirrorVisibilityLaw
    (setup : CorridorMirrorSetup) : Prop where
  virtual_image_preserves_distance_to_M :
    ∀ distance : LengthQuantity,
      physicalDistance
          (setup.mirrorM.reflectPoint (setup.burglarPositionAt distance))
          setup.mirrorM.center =
        physicalDistance (setup.burglarPositionAt distance)
          setup.mirrorM.center
  visible_iff_unobstructed_image_ray :
    ∀ distance : LengthQuantity,
      0 ≤ lengthInMetres distance →
        (setup.guardCanSeeBurglarAt distance ↔
          HasUnobstructedImageRay setup distance)
  unobstructed_image_ray_iff_wall_clearance :
    ∀ distance : LengthQuantity,
      0 ≤ lengthInMetres distance →
        (HasUnobstructedImageRay setup distance ↔
          UnfoldedSightLineClearsWallEdge setup distance)

/--
`distance` is where `S` first sees the approaching burglar: she is visible
there, but was not visible at any larger nonnegative distance from `M`.
-/
def IsFirstVisibleDistance
    (setup : CorridorMirrorSetup) (distance : LengthQuantity) : Prop :=
  0 ≤ lengthInMetres distance ∧
    setup.guardCanSeeBurglarAt distance ∧
    ∀ earlierDistance : LengthQuantity,
      0 ≤ lengthInMetres earlierDistance →
      lengthInMetres distance < lengthInMetres earlierDistance →
        ¬setup.guardCanSeeBurglarAt earlierDistance

/-- The four distance choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- SI-metre readout printed beside an answer label. -/
def AnswerChoice.distanceInMetres : AnswerChoice → ℝ
  | .A => 3
  | .B => 5 / 2
  | .C => 2
  | .D => 3 / 2

/-- A physical distance agrees with the distance printed for a choice. -/
def MatchesAnswerChoice
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  lengthInMetres distance = choice.distanceInMetres

/--
The grazing method-of-images ray and the three equal corridor spans give the
similar-triangle relation that the first-visible distance is half of `d`.
This is a derived result, not a field of the figure or optics assumptions.
-/
lemma first_visible_distance_is_half_d
    (setup : CorridorMirrorSetup)
    (figure : MatchesCorridorFigure setup)
    (optics : ObeysFinitePlaneMirrorVisibilityLaw setup)
    (distance : LengthQuantity)
    (firstVisible : IsFirstVisibleDistance setup distance) :
    lengthInMetres distance = lengthInMetres setup.d / 2 := by
  rcases firstVisible with ⟨distance_nonnegative, visible, first_visible⟩
  have near_span :
      nearHorizontalSpanInMetres setup = lengthInMetres setup.d := by
    rw [nearHorizontalSpanInMetres, figure.first_horizontal_span]
  have far_span :
      farHorizontalSpanInMetres setup = lengthInMetres setup.d := by
    rw [farHorizontalSpanInMetres, figure.second_horizontal_span]
  have vertical_span :
      verticalSpanInMetres setup = lengthInMetres setup.d := by
    rw [verticalSpanInMetres, figure.vertical_span]
  have clears_at_distance :
      UnfoldedSightLineClearsWallEdge setup distance :=
    (optics.unobstructed_image_ray_iff_wall_clearance distance
      distance_nonnegative).mp
      ((optics.visible_iff_unobstructed_image_ray distance
        distance_nonnegative).mp visible)
  have distance_at_most_half :
      lengthInMetres distance ≤ 3 / 2 := by
    rw [UnfoldedSightLineClearsWallEdge, near_span, far_span, vertical_span,
      figure.d_readout] at clears_at_distance
    norm_num at clears_at_distance ⊢
    linarith
  have half_at_most_distance :
      3 / 2 ≤ lengthInMetres distance := by
    by_contra not_half_at_most
    have distance_strictly_below_half :
        lengthInMetres distance < 3 / 2 := lt_of_not_ge not_half_at_most
    let halfDistance : LengthQuantity := metres (3 / 2)
    have half_readout : lengthInMetres halfDistance = 3 / 2 := by
      simp [halfDistance, lengthInMetres, metres, toDimensionful_apply_apply]
    have half_nonnegative : 0 ≤ lengthInMetres halfDistance := by
      rw [half_readout]
      norm_num
    have clears_at_half :
        UnfoldedSightLineClearsWallEdge setup halfDistance := by
      rw [UnfoldedSightLineClearsWallEdge, half_readout, near_span, far_span,
        vertical_span, figure.d_readout]
      norm_num
    have visible_at_half : setup.guardCanSeeBurglarAt halfDistance :=
      (optics.visible_iff_unobstructed_image_ray halfDistance
        half_nonnegative).mpr
        ((optics.unobstructed_image_ray_iff_wall_clearance halfDistance
          half_nonnegative).mpr clears_at_half)
    exact
      (first_visible halfDistance half_nonnegative
        (by simpa [half_readout] using distance_strictly_below_half))
        visible_at_half
  rw [figure.d_readout]
  linarith

/--
For `d = 3.0 m`, the burglar is first visible at `d / 2 = 1.5 m` from the
mirror, which is answer choice D.

Blueprint: `thm:physics:phyx_mini_0162:target`.
-/
theorem problem_phyx_mini_0162
    (setup : CorridorMirrorSetup)
    (figure : MatchesCorridorFigure setup)
    (optics : ObeysFinitePlaneMirrorVisibilityLaw setup)
    (distance : LengthQuantity)
    (firstVisible : IsFirstVisibleDistance setup distance) :
    physicalDistance (setup.burglarPositionAt distance)
          setup.mirrorM.center = metres (3 / 2) ∧
      MatchesAnswerChoice distance .D := by
  have distance_readout :
      lengthInMetres distance = 3 / 2 := by
    rw [first_visible_distance_is_half_d setup figure optics distance
      firstVisible, figure.d_readout]
  have distance_eq : distance = metres (3 / 2) := by
    apply (toDimensionful SI).symm.injective
    apply WithDim.ext
    change (distance SI).val = _
    simpa [lengthInMetres, metres, toDimensionful_apply_apply] using
      distance_readout
  constructor
  · rw [figure.burglar_distance_parameter distance firstVisible.1, distance_eq]
  · simpa [MatchesAnswerChoice, AnswerChoice.distanceInMetres] using
      distance_readout

end PhyXMiniProblems.ProblemPhyXMini0162
