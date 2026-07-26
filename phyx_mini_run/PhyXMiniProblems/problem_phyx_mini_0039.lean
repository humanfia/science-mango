import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0039

open Dimension

/-!
# Santa's image in a silvered spherical ornament

The ornament is modeled as a convex spherical mirror in the paraxial regime.
The horizontal coordinate increases from Santa, through the mirror vertex,
toward the virtual image and the center of curvature `C`.  Signed mirror
distances use the Gaussian convention: object distance is positive in front
of the mirror, while the radius, focal length, and virtual-image distance of
this convex mirror are negative.

All distances and heights are physical lengths.  Real numbers occur only as
their scalar centimeter readouts.
-/

/-- A signed physical length, independent of the unit in which it is read. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices whose length component is the centimeter used in the figure. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar centimeter readout of a dimensionful length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The two spherical-mirror types as viewed from the incident-light side. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/--
Labeled locations on the common optic axis in the primary figure.
`imageBasePrime` is the base of the virtual image arrow `y'`, and
`centerOfCurvatureC` is the point explicitly labeled `C`.
-/
inductive AxisLocation where
  | objectBase
  | mirrorVertex
  | imageBasePrime
  | centerOfCurvatureC
  deriving DecidableEq, Repr

/--
The dimensionful quantities in the spherical-mirror diagram.

The fields `objectDistance` and `imageDistance` are the signed quantities
labeled `s` and `s'`; `objectHeight` and `imageHeight` are the signed
transverse quantities labeled `y` and `y'`.
-/
structure OrnamentMirrorSetup where
  mirrorKind : SphericalMirrorKind
  axisPosition : AxisLocation → LengthQuantity
  ornamentDiameter : LengthQuantity
  radiusOfCurvature : LengthQuantity
  focalLength : LengthQuantity
  objectDistance : LengthQuantity
  imageDistance : LengthQuantity
  objectHeight : LengthQuantity
  imageHeight : LengthQuantity

/--
Numerical readouts supplied by the problem and the annotations in the primary
figure: diameter `7.20 cm`, `R = -3.60 cm`, `f = -1.80 cm`, object distance
`s = 75.0 cm`, and Santa's height `y = 1.6 m = 160 cm`.

No image distance or image height is specified here.
-/
structure MatchesFigureReadouts (setup : OrnamentMirrorSetup) : Prop where
  mirror_is_convex : setup.mirrorKind = .convex
  diameter : lengthInCentimeters setup.ornamentDiameter = 36 / 5
  radius : lengthInCentimeters setup.radiusOfCurvature = -(18 / 5)
  focal_length : lengthInCentimeters setup.focalLength = -(9 / 5)
  object_distance : lengthInCentimeters setup.objectDistance = 75
  object_height : lengthInCentimeters setup.objectHeight = 160

/--
Geometry encoded by the figure's optic axis.  With coordinates increasing to
the right, Santa is in front of the mirror while the virtual image and `C` are
behind it.  The signed distances are measured from these labeled positions.
-/
structure HasDepictedAxisGeometry (setup : OrnamentMirrorSetup) : Prop where
  object_before_vertex :
    lengthInCentimeters (setup.axisPosition .objectBase) <
      lengthInCentimeters (setup.axisPosition .mirrorVertex)
  vertex_before_virtual_image :
    lengthInCentimeters (setup.axisPosition .mirrorVertex) <
      lengthInCentimeters (setup.axisPosition .imageBasePrime)
  vertex_before_center_C :
    lengthInCentimeters (setup.axisPosition .mirrorVertex) <
      lengthInCentimeters (setup.axisPosition .centerOfCurvatureC)
  object_distance_geometry :
    lengthInCentimeters setup.objectDistance =
      lengthInCentimeters (setup.axisPosition .mirrorVertex) -
        lengthInCentimeters (setup.axisPosition .objectBase)
  image_distance_geometry :
    lengthInCentimeters setup.imageDistance =
      lengthInCentimeters (setup.axisPosition .mirrorVertex) -
        lengthInCentimeters (setup.axisPosition .imageBasePrime)
  curvature_radius_geometry :
    lengthInCentimeters setup.radiusOfCurvature =
      lengthInCentimeters (setup.axisPosition .mirrorVertex) -
        lengthInCentimeters (setup.axisPosition .centerOfCurvatureC)

/--
The geometric and paraxial governing laws used for the silvered spherical
ornament.  They state `R = -D/2`, `f = R/2`, the Gaussian mirror equation
`1/f = 1/s + 1/s'`, and the signed transverse-magnification law
`y'/y = -s'/s`.  The last two are written without division.

These are general modeling relations and contain no numerical image answer.
-/
structure SatisfiesParaxialMirrorLaws (setup : OrnamentMirrorSetup) : Prop where
  ornament_radius_from_diameter :
    2 * lengthInCentimeters setup.radiusOfCurvature =
      -lengthInCentimeters setup.ornamentDiameter
  spherical_mirror_focal_length :
    2 * lengthInCentimeters setup.focalLength =
      lengthInCentimeters setup.radiusOfCurvature
  gaussian_mirror_equation :
    lengthInCentimeters setup.focalLength *
        (lengthInCentimeters setup.objectDistance +
          lengthInCentimeters setup.imageDistance) =
      lengthInCentimeters setup.objectDistance *
        lengthInCentimeters setup.imageDistance
  transverse_magnification :
    lengthInCentimeters setup.imageHeight *
        lengthInCentimeters setup.objectDistance =
      -(lengthInCentimeters setup.objectHeight *
        lengthInCentimeters setup.imageDistance)

/-- The four image-height choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The scalar centimeter value displayed beside each answer choice. -/
def answerHeightInCentimeters : AnswerChoice → ℝ
  | .A => 92 / 25
  | .B => 19 / 5
  | .C => 183 / 50
  | .D => 101 / 20

/--
The usual half-open bin for rounding a centimeter value to the displayed
nearest tenth.  Including the lower endpoint makes `3.75 cm` round to
`3.8 cm`, while excluding the upper endpoint keeps the bins disjoint.
-/
def RoundsToNearestTenth
    (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  answerHeightInCentimeters choice - 1 / 20 ≤
      lengthInCentimeters height ∧
    lengthInCentimeters height <
      answerHeightInCentimeters choice + 1 / 20

/--
The Gaussian mirror equation determines the signed virtual-image distance
`s' = -225/128 cm`.
-/
lemma virtualImageDistance_eq
    (setup : OrnamentMirrorSetup)
    (_figure : MatchesFigureReadouts setup)
    (_geometry : HasDepictedAxisGeometry setup)
    (_laws : SatisfiesParaxialMirrorLaws setup) :
    lengthInCentimeters setup.imageDistance = -(225 / 128) := by
  have h := _laws.gaussian_mirror_equation
  rw [_figure.focal_length, _figure.object_distance] at h
  norm_num at h ⊢
  linarith

/--
The mirror equation and transverse-magnification law determine the exact
upright image height `y' = 15/4 cm`.
-/
lemma imageHeight_eq
    (setup : OrnamentMirrorSetup)
    (_figure : MatchesFigureReadouts setup)
    (_geometry : HasDepictedAxisGeometry setup)
    (_laws : SatisfiesParaxialMirrorLaws setup) :
    lengthInCentimeters setup.imageHeight = 15 / 4 := by
  have h_distance := virtualImageDistance_eq setup _figure _geometry _laws
  have h := _laws.transverse_magnification
  rw [_figure.object_distance, _figure.object_height, h_distance] at h
  norm_num at h ⊢
  linarith

/--
Santa's image is exactly `15/4 cm = 3.75 cm` tall, which is displayed as
`3.8 cm`, answer choice B, to the nearest tenth.

This formalizes `thm:physics:phyx_mini_0039:target`.
-/
theorem problem_phyx_mini_0039
    (setup : OrnamentMirrorSetup)
    (_figure : MatchesFigureReadouts setup)
    (_geometry : HasDepictedAxisGeometry setup)
    (_laws : SatisfiesParaxialMirrorLaws setup) :
    lengthInCentimeters setup.imageHeight = 15 / 4 ∧
      RoundsToNearestTenth setup.imageHeight .B := by
  have h_height := imageHeight_eq setup _figure _geometry _laws
  constructor
  · exact h_height
  · norm_num [RoundsToNearestTenth, answerHeightInCentimeters, h_height]

end PhyXMiniProblems.ProblemPhyXMini0039
