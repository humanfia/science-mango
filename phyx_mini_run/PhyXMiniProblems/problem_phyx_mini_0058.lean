import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0058

open Dimension

/-!
# Focal length of a stamp collector's magnifying lens

The primary figure shows a double-convex converging lens above a stamp.  Light
travels from the stamp through the lens plane; the backward extensions of the
refracted rays meet at an upright virtual image on the stamp side of the lens.
The signed Gaussian convention is used: the real-object distance `s` is
positive, while the virtual-image distance `s'` is negative.

All axial locations and optical distances are dimensionful physical lengths.
Real numbers are used only for signed centimeter readouts and for the
dimensionless transverse magnification.
-/

/-- A signed physical length represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- Labels attached to locations in the magnifying-lens figure. -/
inductive FigureLocation where
  | stamp
  | lensPlane
  | focalPoint
  | virtualImage
  deriving DecidableEq, Repr

/-- Whether a pictured ray is an actual solid ray or a dashed backward extension. -/
inductive RayStyle where
  | actualSolid
  | virtualDashed
  deriving DecidableEq, Repr

/-- Optical action of the thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Geometric profile drawn for the lens. -/
inductive LensProfile where
  | doubleConvex
  | other
  deriving DecidableEq, Repr

/--
The dimensionful quantities and labeled geometry of the stamp magnifier.

`objectDistance` is the positive figure label `s`; `signedImageDistance` is
the signed label `s'`; and `focalLength` is the positive distance `f` from the
lens plane to the displayed focal point.  `transverseMagnification` is signed
and dimensionless, so an upright virtual image has positive magnification.
-/
structure StampMagnifierSetup where
  axisPosition : FigureLocation → LengthQuantity
  rayLandmarks : RayStyle → List FigureLocation
  lensKind : ThinLensKind
  lensProfile : LensProfile
  objectDistance : LengthQuantity
  signedImageDistance : LengthQuantity
  focalLength : LengthQuantity
  transverseMagnification : ℝ

/--
Numerical information in the problem statement: the lens is `2.0 cm` above
the stamp and its signed transverse magnification is `+4.0`.

No focal-length value occurs in these data.
-/
structure MatchesProblemReadouts (setup : StampMagnifierSetup) : Prop where
  object_distance : lengthInCentimeters setup.objectDistance = 2
  transverse_magnification : setup.transverseMagnification = 4

/--
Information read directly from the primary figure.  Coordinates increase from
the stamp side through the lens toward the outgoing side.  Thus the virtual
image lies farther on the incoming side than the stamp, while the displayed
focal point lies beyond the lens plane.  The annotation `s' = -4.0 s` is kept
as a figure readout rather than treated as the requested focal-length answer.
-/
structure MatchesMagnifierFigure (setup : StampMagnifierSetup) : Prop where
  depicted_lens_kind : setup.lensKind = .converging
  depicted_lens_profile : setup.lensProfile = .doubleConvex
  virtual_image_before_stamp :
    lengthInCentimeters (setup.axisPosition .virtualImage) <
      lengthInCentimeters (setup.axisPosition .stamp)
  stamp_before_lens :
    lengthInCentimeters (setup.axisPosition .stamp) <
      lengthInCentimeters (setup.axisPosition .lensPlane)
  lens_before_focal_point :
    lengthInCentimeters (setup.axisPosition .lensPlane) <
      lengthInCentimeters (setup.axisPosition .focalPoint)
  object_distance_geometry :
    lengthInCentimeters setup.objectDistance =
      lengthInCentimeters (setup.axisPosition .lensPlane) -
        lengthInCentimeters (setup.axisPosition .stamp)
  signed_image_distance_geometry :
    lengthInCentimeters setup.signedImageDistance =
      lengthInCentimeters (setup.axisPosition .virtualImage) -
        lengthInCentimeters (setup.axisPosition .lensPlane)
  focal_length_geometry :
    lengthInCentimeters setup.focalLength =
      lengthInCentimeters (setup.axisPosition .focalPoint) -
        lengthInCentimeters (setup.axisPosition .lensPlane)
  displayed_image_distance_relation :
    lengthInCentimeters setup.signedImageDistance =
      -4 * lengthInCentimeters setup.objectDistance
  stamp_on_solid_rays : .stamp ∈ setup.rayLandmarks .actualSolid
  lens_on_solid_rays : .lensPlane ∈ setup.rayLandmarks .actualSolid
  focal_point_on_solid_rays : .focalPoint ∈ setup.rayLandmarks .actualSolid
  lens_on_dashed_extensions : .lensPlane ∈ setup.rayLandmarks .virtualDashed
  virtual_image_on_dashed_extensions :
    .virtualImage ∈ setup.rayLandmarks .virtualDashed

/-- The real-object, virtual-image, magnifying branch depicted in the figure. -/
structure HasPhysicalOpticalBranch (setup : StampMagnifierSetup) : Prop where
  object_distance_positive : 0 < lengthInCentimeters setup.objectDistance
  virtual_image_distance_negative :
    lengthInCentimeters setup.signedImageDistance < 0
  converging_focal_length_positive : 0 < lengthInCentimeters setup.focalLength
  magnification_greater_than_one : 1 < setup.transverseMagnification

/--
The paraxial governing laws for the setup, stated in every choice of units.
The first field is the denominator-free form of
`1 / f = 1 / s + 1 / s'`.  The second is the denominator-free signed
magnification law `m = -s' / s`.

These fields are general physical laws and contain no numerical focal-length
answer.
-/
structure SatisfiesParaxialThinLensLaws (setup : StampMagnifierSetup) : Prop where
  gaussian_thin_lens_equation :
    ∀ units : UnitChoices,
      (setup.focalLength units).val *
          ((setup.objectDistance units).val +
            (setup.signedImageDistance units).val) =
        (setup.objectDistance units).val *
          (setup.signedImageDistance units).val
  signed_transverse_magnification :
    ∀ units : UnitChoices,
      setup.transverseMagnification * (setup.objectDistance units).val =
        -(setup.signedImageDistance units).val

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The focal-length readout printed beside each answer choice, in centimeters. -/
def answerFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => 7 / 5
  | .B => 8 / 5
  | .C => 27 / 10
  | .D => 12 / 5

/-- Agreement with a displayed focal length rounded to the nearest tenth centimeter. -/
def RoundsToNearestTenthCentimeter
    (length : LengthQuantity) (choice : AnswerChoice) : Prop :=
  answerFocalLengthInCentimeters choice - 1 / 20 ≤
      lengthInCentimeters length ∧
    lengthInCentimeters length <
      answerFocalLengthInCentimeters choice + 1 / 20

/-- A selected option is strictly closer to the exact focal length than every rival. -/
def IsClosestFocalLengthAnswer
    (length : LengthQuantity) (selected : AnswerChoice) : Prop :=
  ∀ other, other ≠ selected →
    |lengthInCentimeters length - answerFocalLengthInCentimeters selected| <
      |lengthInCentimeters length - answerFocalLengthInCentimeters other|

/--
The signed magnification law and the two problem readouts determine the
virtual-image distance as `s' = -8 cm`.
-/
lemma signedImageDistance_eq_neg_eight
    (setup : StampMagnifierSetup)
    (_data : MatchesProblemReadouts setup)
    (_laws : SatisfiesParaxialThinLensLaws setup) :
    lengthInCentimeters setup.signedImageDistance = -8 := by
  have hMagnification :=
    _laws.signed_transverse_magnification centimeterUnitChoices
  change
    setup.transverseMagnification *
        lengthInCentimeters setup.objectDistance =
      -lengthInCentimeters setup.signedImageDistance at hMagnification
  rw [_data.transverse_magnification, _data.object_distance] at hMagnification
  linarith

/--
The Gaussian thin-lens equation then determines the exact focal length
`f = 8/3 cm`.
-/
lemma focalLength_eq_eight_thirds
    (setup : StampMagnifierSetup)
    (_data : MatchesProblemReadouts setup)
    (_laws : SatisfiesParaxialThinLensLaws setup) :
    lengthInCentimeters setup.focalLength = 8 / 3 := by
  have hImageDistance :=
    signedImageDistance_eq_neg_eight setup _data _laws
  have hLensEquation :=
    _laws.gaussian_thin_lens_equation centimeterUnitChoices
  change
    lengthInCentimeters setup.focalLength *
        (lengthInCentimeters setup.objectDistance +
          lengthInCentimeters setup.signedImageDistance) =
      lengthInCentimeters setup.objectDistance *
        lengthInCentimeters setup.signedImageDistance at hLensEquation
  rw [_data.object_distance, hImageDistance] at hLensEquation
  norm_num at hLensEquation ⊢
  linarith

/--
The magnifying lens has exact focal length `8/3 cm`.  This rounds to `2.7 cm`,
which is uniquely closest among the displayed answers and hence is choice C.

This formalizes `thm:physics:phyx_mini_0058:target`.
-/
theorem problem_phyx_mini_0058
    (setup : StampMagnifierSetup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesMagnifierFigure setup)
    (_physical : HasPhysicalOpticalBranch setup)
    (_laws : SatisfiesParaxialThinLensLaws setup) :
    lengthInCentimeters setup.focalLength = 8 / 3 ∧
      RoundsToNearestTenthCentimeter setup.focalLength .C ∧
      IsClosestFocalLengthAnswer setup.focalLength .C := by
  have hFocalLength := focalLength_eq_eight_thirds setup _data _laws
  refine ⟨hFocalLength, ?_, ?_⟩
  · simp only [RoundsToNearestTenthCentimeter, answerFocalLengthInCentimeters]
    rw [hFocalLength]
    norm_num
  · intro other hOther
    rw [hFocalLength]
    cases other with
    | A =>
        norm_num [answerFocalLengthInCentimeters]
    | B =>
        norm_num [answerFocalLengthInCentimeters]
    | C =>
        exact (hOther rfl).elim
    | D =>
        norm_num [answerFocalLengthInCentimeters]

end PhyXMiniProblems.ProblemPhyXMini0058
