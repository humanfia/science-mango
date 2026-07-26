import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0059

open Dimension

/-!
# Image height for an object inside the focus of a concave mirror

The primary figure places a `3.0 cm` upright object `20 cm` in front of a
concave spherical mirror.  The mirror has radius of curvature `80 cm`, so its
displayed focal length is `40 cm`.  The reflected rays diverge, while their
backward extensions meet behind the mirror at an upright virtual image.

All distances and heights are dimension-carrying physical lengths.  Real
numbers occur only as signed scalar readouts in centimeters or as the
dimensionless transverse magnification.
-/

/-- A signed physical length, independent of the unit chosen to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices with centimeters selected as the unit of length. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- Labeled points on the horizontal principal axis in the primary figure. -/
inductive AxialFigurePoint where
  | focalPoint
  | objectBase
  | mirrorVertex
  | virtualImageBase
  deriving DecidableEq, Repr

/-- The spherical-mirror type as viewed from the incident-light side. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Whether reflected rays themselves, or only their backward extensions, meet. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The transverse orientation of the image relative to the object. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- How the reflected rays in the primary figure locate the image. -/
inductive RayConstruction where
  | directIntersection
  | reflectedRaysWithBackwardExtensions
  deriving DecidableEq, Repr

/-- The relation drawn between the mirror plane and principal axis. -/
inductive MirrorPlaneRelation where
  | perpendicularToPrincipalAxis
  | obliqueToPrincipalAxis
  deriving DecidableEq, Repr

/--
The physical quantities and labeled axial positions in the mirror diagram.

`objectDistance` is the positive figure label `s`.  The field
`signedImageDistance` is the signed Gaussian distance `s'`: it is negative for
the pictured virtual image.  The radius field records the positive magnitude
given in the problem.
-/
structure ConcaveMirrorSetup where
  axisPosition : AxialFigurePoint → LengthQuantity
  mirrorKind : SphericalMirrorKind
  imageNature : ImageNature
  imageOrientation : ImageOrientation
  rayConstruction : RayConstruction
  mirrorPlaneRelation : MirrorPlaneRelation
  diagramScaleInterval : LengthQuantity
  radiusOfCurvatureMagnitude : LengthQuantity
  focalLength : LengthQuantity
  objectDistance : LengthQuantity
  signedImageDistance : LengthQuantity
  objectHeight : LengthQuantity
  imageHeight : LengthQuantity
  transverseMagnification : ℝ

/-- The directed centimeter separation of two labels on the principal axis. -/
def axialSeparationCentimeters
    (setup : ConcaveMirrorSetup) (left right : AxialFigurePoint) : ℝ :=
  lengthInCentimeters (setup.axisPosition right) -
    lengthInCentimeters (setup.axisPosition left)

/--
Problem-statement and primary-figure readouts.  These include only supplied
data: the object dimensions and placement, the radius and displayed focal
length, and the qualitative nature and orientation of the pictured image.
The requested image height is deliberately absent.
-/
structure MatchesFigureReadouts (setup : ConcaveMirrorSetup) : Prop where
  mirror_is_concave : setup.mirrorKind = .concave
  object_height_readout : lengthInCentimeters setup.objectHeight = 3
  object_distance_readout : lengthInCentimeters setup.objectDistance = 20
  radius_readout : lengthInCentimeters setup.radiusOfCurvatureMagnitude = 80
  focal_length_readout : lengthInCentimeters setup.focalLength = 40
  scale_interval_readout : lengthInCentimeters setup.diagramScaleInterval = 10
  image_is_virtual : setup.imageNature = .virtual
  image_is_upright : setup.imageOrientation = .upright
  image_located_by_backward_extensions :
    setup.rayConstruction = .reflectedRaysWithBackwardExtensions
  mirror_plane_is_perpendicular :
    setup.mirrorPlaneRelation = .perpendicularToPrincipalAxis
  focus_object_mirror_order :
    lengthInCentimeters (setup.axisPosition .focalPoint) <
        lengthInCentimeters (setup.axisPosition .objectBase) ∧
      lengthInCentimeters (setup.axisPosition .objectBase) <
        lengthInCentimeters (setup.axisPosition .mirrorVertex)
  virtual_image_behind_mirror :
    lengthInCentimeters (setup.axisPosition .mirrorVertex) <
      lengthInCentimeters (setup.axisPosition .virtualImageBase)

/--
The labeled separations agree with the physical distance fields.  Axial
coordinates increase to the right, so a virtual image behind the mirror has
signed Gaussian distance equal to the negative mirror-to-image separation.
-/
structure SatisfiesLabeledAxialGeometry (setup : ConcaveMirrorSetup) : Prop where
  object_distance_geometry :
    lengthInCentimeters setup.objectDistance =
      axialSeparationCentimeters setup .objectBase .mirrorVertex
  focal_length_geometry :
    lengthInCentimeters setup.focalLength =
      axialSeparationCentimeters setup .focalPoint .mirrorVertex
  signed_image_distance_geometry :
    lengthInCentimeters setup.signedImageDistance =
      -axialSeparationCentimeters setup .mirrorVertex .virtualImageBase

/-- Positivity and signed-distance conventions for the depicted optical branch. -/
structure UsesCartesianMirrorSignConvention (setup : ConcaveMirrorSetup) : Prop where
  radius_positive : 0 < lengthInCentimeters setup.radiusOfCurvatureMagnitude
  focal_length_positive : 0 < lengthInCentimeters setup.focalLength
  object_distance_positive : 0 < lengthInCentimeters setup.objectDistance
  object_height_positive : 0 < lengthInCentimeters setup.objectHeight
  image_height_positive : 0 < lengthInCentimeters setup.imageHeight
  virtual_image_has_negative_distance :
    setup.imageNature = .virtual →
      lengthInCentimeters setup.signedImageDistance < 0

/--
The focal length of a spherical mirror is half the magnitude of its radius of
curvature.  Requiring the relation in every unit choice makes the governing
law independent of the centimeter readout used by the figure.
-/
def SatisfiesSphericalMirrorFocalLaw (setup : ConcaveMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    (setup.radiusOfCurvatureMagnitude units).val =
      2 * (setup.focalLength units).val

/--
The signed Gaussian mirror equation `1/f = 1/p + 1/q`, in the division-free
dimensionally homogeneous form `f * (p + q) = p * q` and in every unit system.
-/
def SatisfiesGaussianMirrorEquation (setup : ConcaveMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.focalLength units *
        (setup.objectDistance units + setup.signedImageDistance units) =
      setup.objectDistance units * setup.signedImageDistance units

/--
The signed transverse-magnification law `m = -q/p`, written without division.
The magnification is dimensionless, while `p` and `q` are signed lengths.
-/
def SatisfiesSignedMagnificationLaw (setup : ConcaveMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.transverseMagnification * (setup.objectDistance units).val =
      -(setup.signedImageDistance units).val

/-- The image-height law `hᵢ = m hₒ`, required in every unit system. -/
def SatisfiesImageHeightLaw (setup : ConcaveMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    (setup.imageHeight units).val =
      setup.transverseMagnification * (setup.objectHeight units).val

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The image height in centimeters printed beside each answer choice. -/
def answerHeightInCentimeters : AnswerChoice → ℝ
  | .A => 7 / 5
  | .B => 28 / 5
  | .C => 6
  | .D => 12 / 5

/-- Exact agreement between a physical image height and a displayed choice. -/
def MatchesAnswer (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters height = answerHeightInCentimeters choice

/--
The governing mirror and magnification equations determine the unprinted
intermediate quantities: the virtual image distance is `-40 cm` and the
upright transverse magnification is `2`.
-/
lemma signed_image_distance_and_magnification
    (setup : ConcaveMirrorSetup)
    (h_readouts : MatchesFigureReadouts setup)
    (h_geometry : SatisfiesLabeledAxialGeometry setup)
    (h_sign : UsesCartesianMirrorSignConvention setup)
    (h_focal : SatisfiesSphericalMirrorFocalLaw setup)
    (h_imaging : SatisfiesGaussianMirrorEquation setup)
    (h_magnification : SatisfiesSignedMagnificationLaw setup) :
    lengthInCentimeters setup.signedImageDistance = -40 ∧
      setup.transverseMagnification = 2 := by
  have h_imaging_cm :=
    congrArg WithDim.val (h_imaging centimeterUnitChoices)
  change
    lengthInCentimeters setup.focalLength *
          (lengthInCentimeters setup.objectDistance +
            lengthInCentimeters setup.signedImageDistance) =
        lengthInCentimeters setup.objectDistance *
          lengthInCentimeters setup.signedImageDistance
    at h_imaging_cm
  have h_image_distance :
      lengthInCentimeters setup.signedImageDistance = -40 := by
    nlinarith [h_imaging_cm, h_readouts.focal_length_readout,
      h_readouts.object_distance_readout]
  have h_magnification_cm := h_magnification centimeterUnitChoices
  change
    setup.transverseMagnification *
          lengthInCentimeters setup.objectDistance =
        -lengthInCentimeters setup.signedImageDistance
    at h_magnification_cm
  constructor
  · exact h_image_distance
  · nlinarith [h_magnification_cm, h_readouts.object_distance_readout,
      h_image_distance]

/--
The virtual image is twice as tall as the `3.0 cm` object, hence has exact
height `6.0 cm`, which is answer choice C.

This formalizes `thm:physics:phyx_mini_0059:target`.
-/
theorem problem_phyx_mini_0059
    (setup : ConcaveMirrorSetup)
    (h_readouts : MatchesFigureReadouts setup)
    (h_geometry : SatisfiesLabeledAxialGeometry setup)
    (h_sign : UsesCartesianMirrorSignConvention setup)
    (h_focal : SatisfiesSphericalMirrorFocalLaw setup)
    (h_imaging : SatisfiesGaussianMirrorEquation setup)
    (h_magnification : SatisfiesSignedMagnificationLaw setup)
    (h_height : SatisfiesImageHeightLaw setup) :
    lengthInCentimeters setup.imageHeight = 6 ∧
      MatchesAnswer setup.imageHeight .C := by
  obtain ⟨_, h_magnification_value⟩ :=
    signed_image_distance_and_magnification setup h_readouts h_geometry h_sign
      h_focal h_imaging h_magnification
  have h_height_cm := h_height centimeterUnitChoices
  change
    lengthInCentimeters setup.imageHeight =
      setup.transverseMagnification *
        lengthInCentimeters setup.objectHeight
    at h_height_cm
  have h_image_height : lengthInCentimeters setup.imageHeight = 6 := by
    nlinarith [h_height_cm, h_magnification_value,
      h_readouts.object_height_readout]
  constructor
  · exact h_image_height
  · simpa [MatchesAnswer, answerHeightInCentimeters] using h_image_height

end PhyXMiniProblems.ProblemPhyXMini0059
