import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0140

open Dimension

/-!
# Magnification of an object inside a concave mirror's focus

A `1.00 cm`-high object is `10.0 cm` in front of a concave spherical mirror
whose radius of curvature has magnitude `30.0 cm`.  The primary image labels
the center of curvature `C`, the focus `F`, the object base `O`, the mirror
aperture/vertex `A`, and the upright virtual image `I`.

Lengths below are dimension-carrying physical quantities.  Real numbers are
used only for their scalar readouts in centimeters and for the dimensionless
signed transverse magnification.
-/

/-- A signed physical length, independent of the unit chosen to read it. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : OpticalLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- The five lettered points on the horizontal principal axis. -/
inductive AxialFigurePoint where
  | centerC
  | focusF
  | objectO
  | apertureA
  | imageI
  deriving DecidableEq, Repr

/-- The optical type of the spherical mirror viewed from the incident side. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Whether the physical rays or only their backward extensions meet. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The image orientation relative to the upright object. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- The side of the mirror on which a depicted object lies. -/
inductive MirrorSide where
  | incident
  | behindMirror
  deriving DecidableEq, Repr

/-- The three numbered principal rays shown in the primary image. -/
inductive PrincipalRay where
  | rayOne
  | rayTwo
  | rayThree
  deriving DecidableEq, Repr

/-- The standard paraxial behavior represented by a principal ray. -/
inductive PrincipalRayBehavior where
  | parallelThenThroughFocus
  | throughFocusThenParallel
  | throughCenterThenRetraces
  deriving DecidableEq, Repr

/--
The physical mirror setup together with the lettered axial geometry and the
qualitative ray information in the source image.

`objectDistance` and `radiusOfCurvatureMagnitude` are positive magnitudes.
`signedImageDistance` follows the Gaussian convention and is negative for the
pictured virtual image.  The unknown `transverseMagnification` is a signed,
dimensionless scalar; it is not initialized with an answer choice.
-/
structure ConcaveMirrorSetup where
  axisPosition : AxialFigurePoint → OpticalLength
  mirrorKind : SphericalMirrorKind
  observerSide : MirrorSide
  objectSide : MirrorSide
  imageSide : MirrorSide
  imageNature : ImageNature
  imageOrientation : ImageOrientation
  rayBehavior : PrincipalRay → PrincipalRayBehavior
  hasDashedBackwardExtension : PrincipalRay → Bool
  radiusOfCurvatureMagnitude : OpticalLength
  focalLength : OpticalLength
  objectDistance : OpticalLength
  signedImageDistance : OpticalLength
  objectHeight : OpticalLength
  transverseMagnification : ℝ

/-- The directed centimeter separation between two lettered axis points. -/
def axialSeparationInCentimeters
    (setup : ConcaveMirrorSetup)
    (left right : AxialFigurePoint) : ℝ :=
  lengthInCentimeters (setup.axisPosition right) -
    lengthInCentimeters (setup.axisPosition left)

/--
The numerical data supplied by the problem statement.  No focal length, image
distance, or magnification value is included here.
-/
structure MatchesStatedReadouts (setup : ConcaveMirrorSetup) : Prop where
  mirror_is_concave : setup.mirrorKind = .concave
  object_height_in_centimeters :
    lengthInCentimeters setup.objectHeight = 1
  object_distance_in_centimeters :
    lengthInCentimeters setup.objectDistance = 10
  radius_in_centimeters :
    lengthInCentimeters setup.radiusOfCurvatureMagnitude = 30

/-!
Primary-image readouts.  In the image itself the upright object is based at
`O`, while the green mirror intersects the principal axis at `A`; this is why
the physical distance fields below are attached to those literal labels.
-/
structure MatchesPrimaryFigure (setup : ConcaveMirrorSetup) : Prop where
  observer_on_incident_side : setup.observerSide = .incident
  object_on_incident_side : setup.objectSide = .incident
  image_behind_mirror : setup.imageSide = .behindMirror
  image_is_virtual : setup.imageNature = .virtual
  image_is_upright : setup.imageOrientation = .upright
  lettered_point_order :
    lengthInCentimeters (setup.axisPosition .centerC) <
        lengthInCentimeters (setup.axisPosition .focusF) ∧
      lengthInCentimeters (setup.axisPosition .focusF) <
        lengthInCentimeters (setup.axisPosition .objectO) ∧
      lengthInCentimeters (setup.axisPosition .objectO) <
        lengthInCentimeters (setup.axisPosition .apertureA) ∧
      lengthInCentimeters (setup.axisPosition .apertureA) <
        lengthInCentimeters (setup.axisPosition .imageI)
  center_to_aperture_is_radius :
    axialSeparationInCentimeters setup .centerC .apertureA =
      lengthInCentimeters setup.radiusOfCurvatureMagnitude
  focus_to_aperture_is_focal_length :
    axialSeparationInCentimeters setup .focusF .apertureA =
      lengthInCentimeters setup.focalLength
  object_to_aperture_is_object_distance :
    axialSeparationInCentimeters setup .objectO .apertureA =
      lengthInCentimeters setup.objectDistance
  image_position_gives_signed_distance :
    lengthInCentimeters setup.signedImageDistance =
      -axialSeparationInCentimeters setup .apertureA .imageI
  first_ray_behavior :
    setup.rayBehavior .rayOne = .parallelThenThroughFocus
  second_ray_behavior :
    setup.rayBehavior .rayTwo = .throughFocusThenParallel
  third_ray_behavior :
    setup.rayBehavior .rayThree = .throughCenterThenRetraces
  first_ray_has_dashed_extension :
    setup.hasDashedBackwardExtension .rayOne = true
  second_ray_has_dashed_extension :
    setup.hasDashedBackwardExtension .rayTwo = true
  third_ray_has_dashed_extension :
    setup.hasDashedBackwardExtension .rayThree = true

/-- Positivity and signed-distance conditions for the depicted optical branch. -/
structure UsesCartesianMirrorSignConvention (setup : ConcaveMirrorSetup) : Prop where
  radius_positive :
    0 < lengthInCentimeters setup.radiusOfCurvatureMagnitude
  focal_length_positive :
    0 < lengthInCentimeters setup.focalLength
  object_distance_positive :
    0 < lengthInCentimeters setup.objectDistance
  object_height_positive :
    0 < lengthInCentimeters setup.objectHeight
  virtual_image_has_negative_distance :
    setup.imageNature = .virtual →
      lengthInCentimeters setup.signedImageDistance < 0

/--
For a spherical mirror, the radius-of-curvature magnitude is twice the
positive paraxial focal length.  The relation is required in every unit system.
-/
def SatisfiesSphericalMirrorFocalLaw (setup : ConcaveMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    (setup.radiusOfCurvatureMagnitude units).val =
      2 * (setup.focalLength units).val

/--
The signed Gaussian mirror equation `1/f = 1/dₒ + 1/dᵢ`, written in the
division-free dimensionally homogeneous form `f(dₒ + dᵢ) = dₒ dᵢ`.
-/
def SatisfiesGaussianMirrorEquation (setup : ConcaveMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.focalLength units *
        (setup.objectDistance units + setup.signedImageDistance units) =
      setup.objectDistance units * setup.signedImageDistance units

/--
The signed transverse-magnification law `m = -dᵢ/dₒ`, written without
division.  It relates the dimensionless magnification to signed lengths.
-/
def SatisfiesSignedMagnificationLaw (setup : ConcaveMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.transverseMagnification * (setup.objectDistance units).val =
      -(setup.signedImageDistance units).val

/-- The labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless signed magnification printed beside each answer. -/
def AnswerChoice.magnification : AnswerChoice → ℝ
  | .A => 2
  | .B => 4
  | .C => 3
  | .D => 5

/-- Exact agreement between a signed magnification and a displayed choice. -/
def MatchesAnswer (magnification : ℝ) (choice : AnswerChoice) : Prop :=
  magnification = choice.magnification

/--
The radius law and Gaussian mirror equation give the two analytic intermediate
values `f = 15 cm` and `dᵢ = -30 cm`.
-/
lemma focal_length_and_signed_image_distance
    (setup : ConcaveMirrorSetup)
    (h_readouts : MatchesStatedReadouts setup)
    (h_sign : UsesCartesianMirrorSignConvention setup)
    (h_focal : SatisfiesSphericalMirrorFocalLaw setup)
    (h_imaging : SatisfiesGaussianMirrorEquation setup) :
    lengthInCentimeters setup.focalLength = 15 ∧
      lengthInCentimeters setup.signedImageDistance = -30 := by
  have h_focal_cm :
      lengthInCentimeters setup.radiusOfCurvatureMagnitude =
        2 * lengthInCentimeters setup.focalLength := by
    simpa [SatisfiesSphericalMirrorFocalLaw, lengthInCentimeters] using
      h_focal centimeterUnitChoices
  have h_focal_value :
      lengthInCentimeters setup.focalLength = 15 := by
    nlinarith [h_readouts.radius_in_centimeters]
  have h_imaging_dimensional := h_imaging centimeterUnitChoices
  have h_imaging_cm := congrArg WithDim.val h_imaging_dimensional
  simp only [WithDim.withDim_hMul_val, WithDim.val_add] at h_imaging_cm
  have h_image_value :
      lengthInCentimeters setup.signedImageDistance = -30 := by
    change
      lengthInCentimeters setup.focalLength *
          (lengthInCentimeters setup.objectDistance +
            lengthInCentimeters setup.signedImageDistance) =
        lengthInCentimeters setup.objectDistance *
          lengthInCentimeters setup.signedImageDistance at h_imaging_cm
    nlinarith [h_readouts.object_distance_in_centimeters]
  exact ⟨h_focal_value, h_image_value⟩

/--
The signed magnification is therefore `-(-30 cm)/(10 cm) = +3`, so the image
is upright and the recorded answer is choice C.

This formalizes `thm:physics:phyx_mini_0140:target`.
-/
theorem problem_phyx_mini_0140
    (setup : ConcaveMirrorSetup)
    (h_readouts : MatchesStatedReadouts setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_sign : UsesCartesianMirrorSignConvention setup)
    (h_focal : SatisfiesSphericalMirrorFocalLaw setup)
    (h_imaging : SatisfiesGaussianMirrorEquation setup)
    (h_magnification : SatisfiesSignedMagnificationLaw setup) :
    setup.transverseMagnification = 3 ∧
      MatchesAnswer setup.transverseMagnification .C := by
  obtain ⟨_, h_image_value⟩ :=
    focal_length_and_signed_image_distance setup h_readouts h_sign h_focal h_imaging
  have h_magnification_cm :
      setup.transverseMagnification *
          lengthInCentimeters setup.objectDistance =
        -lengthInCentimeters setup.signedImageDistance := by
    simpa [SatisfiesSignedMagnificationLaw, lengthInCentimeters] using
      h_magnification centimeterUnitChoices
  have h_value : setup.transverseMagnification = 3 := by
    nlinarith [h_readouts.object_distance_in_centimeters]
  refine ⟨h_value, ?_⟩
  simpa [MatchesAnswer, AnswerChoice.magnification] using h_value

end PhyXMiniProblems.ProblemPhyXMini0140
