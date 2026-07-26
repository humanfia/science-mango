import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0053

open Dimension

/-!
# Magnification produced by a diverging thin lens

The object distance, signed image distance, focal lengths, axial positions,
and transverse heights are dimensionful physical lengths.  Their scalar
readouts below are taken in centimeters, the unit used in the problem and its
ray diagram.  The Cartesian convention makes the focal length and image
distance negative for the pictured diverging-lens virtual image, while the
object distance is positive.
-/

/-- A signed physical length whose readout changes coherently with unit choice. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The two paraxial thin-lens types, distinguished by focal-length sign. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Whether image rays meet physically or only after backward extension. -/
inductive GeometricalImageKind where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The transverse orientation of an image relative to its object. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- The orientation of the principal optical axis in the source diagram. -/
inductive PrincipalAxisOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Labeled points whose signed axial positions occur in the ray diagram. -/
inductive FigurePoint where
  | objectBase
  | leftFocalPoint
  | virtualImageBase
  | lensCenter
  | rightFocalPoint
  deriving DecidableEq, Repr

/-- The two ray labels printed as `a` and `b` in the primary figure. -/
inductive FigureRayLabel where
  | a
  | b
  deriving DecidableEq, Repr

/-!
The complete physical setup represented in the question and primary image.

`focalLengthMagnitude` is positive, while `signedFocalLength` uses the
Cartesian sign convention.  `objectDistance` is the positive lens-to-object
distance and `signedImageDistance` is negative for a virtual image on the
object side.  Heights are positive magnitudes because the pictured virtual
image is upright.
-/
structure DivergingLensSetup where
  lensKind : ThinLensKind
  imageKind : GeometricalImageKind
  imageOrientation : ImageOrientation
  principalAxisOrientation : PrincipalAxisOrientation
  focalLengthMagnitude : LengthQuantity
  signedFocalLength : LengthQuantity
  objectDistance : LengthQuantity
  signedImageDistance : LengthQuantity
  objectHeight : LengthQuantity
  imageHeight : LengthQuantity
  magnification : ℝ
  axisPosition : FigurePoint → LengthQuantity
  rayIsDrawn : FigureRayLabel → Prop

/-!
Problem and figure readouts.  The primary image places the object `100 cm`
left of the lens and the two focal points `50 cm` from its center.  It depicts
an upright, reduced virtual image between the left focal point and the lens,
and includes both rays labeled `a` and `b`.

The circled `4`, `5`, and `6` in the image are callout markers, not numerical
height or distance measurements, so no values are assigned to the two heights
or to the image location here.
-/
structure MatchesPrimaryFigure (setup : DivergingLensSetup) : Prop where
  lens_is_diverging : setup.lensKind = .diverging
  image_is_virtual : setup.imageKind = .virtual
  image_is_upright : setup.imageOrientation = .upright
  axis_is_horizontal : setup.principalAxisOrientation = .horizontal
  focal_length_magnitude :
    lengthInCentimeters setup.focalLengthMagnitude = 50
  object_distance : lengthInCentimeters setup.objectDistance = 100
  lens_center_at_origin :
    lengthInCentimeters (setup.axisPosition .lensCenter) = 0
  object_position :
    lengthInCentimeters (setup.axisPosition .objectBase) = -100
  left_focal_position :
    lengthInCentimeters (setup.axisPosition .leftFocalPoint) = -50
  right_focal_position :
    lengthInCentimeters (setup.axisPosition .rightFocalPoint) = 50
  virtual_image_between_left_focus_and_lens :
    lengthInCentimeters (setup.axisPosition .leftFocalPoint) <
        lengthInCentimeters (setup.axisPosition .virtualImageBase) ∧
      lengthInCentimeters (setup.axisPosition .virtualImageBase) <
        lengthInCentimeters (setup.axisPosition .lensCenter)
  image_is_reduced :
    0 < lengthInCentimeters setup.imageHeight ∧
      lengthInCentimeters setup.imageHeight <
        lengthInCentimeters setup.objectHeight
  ray_a_is_drawn : setup.rayIsDrawn .a
  ray_b_is_drawn : setup.rayIsDrawn .b

/-!
The Cartesian bookkeeping relating the signed distances used by the imaging
laws to the positive focal-length magnitude and to the axial figure positions.
This states a sign convention, not the requested image distance or
magnification.
-/
structure UsesCartesianSignConvention (setup : DivergingLensSetup) : Prop where
  diverging_focal_length :
    lengthInCentimeters setup.signedFocalLength =
      -lengthInCentimeters setup.focalLengthMagnitude
  object_distance_from_positions :
    lengthInCentimeters setup.objectDistance =
      lengthInCentimeters (setup.axisPosition .lensCenter) -
        lengthInCentimeters (setup.axisPosition .objectBase)
  image_distance_from_positions :
    lengthInCentimeters setup.signedImageDistance =
      lengthInCentimeters (setup.axisPosition .virtualImageBase) -
        lengthInCentimeters (setup.axisPosition .lensCenter)

/-- Qualitative sign conditions for the depicted diverging-lens configuration. -/
structure HasPhysicalSignConfiguration (setup : DivergingLensSetup) : Prop where
  focal_magnitude_positive :
    0 < lengthInCentimeters setup.focalLengthMagnitude
  signed_focal_length_negative :
    lengthInCentimeters setup.signedFocalLength < 0
  object_distance_positive : 0 < lengthInCentimeters setup.objectDistance
  signed_image_distance_negative :
    lengthInCentimeters setup.signedImageDistance < 0
  object_height_positive : 0 < lengthInCentimeters setup.objectHeight

/-!
The paraxial signed thin-lens equation `1/f = 1/s + 1/s'`, expressed in the
dimensionally homogeneous form `f * (s + s') = s * s'` in every unit system.
-/
def ObeysSignedThinLensEquation (setup : DivergingLensSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.signedFocalLength units *
        (setup.objectDistance units + setup.signedImageDistance units) =
      setup.objectDistance units * setup.signedImageDistance units

/-!
The signed transverse-magnification laws `m = -s'/s` and `h_i = m h_o`.
The distance-ratio equation determines the requested dimensionless quantity;
the height equation records its physical interpretation in the ray diagram.
-/
def ObeysTransverseMagnificationLaw (setup : DivergingLensSetup) : Prop :=
  (∀ units : UnitChoices,
      setup.magnification =
        -(setup.signedImageDistance units).val /
          (setup.objectDistance units).val) ∧
    ∀ units : UnitChoices,
      (setup.imageHeight units).val =
        setup.magnification * (setup.objectHeight units).val

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless decimal magnification printed beside each answer choice. -/
def AnswerChoice.magnification : AnswerChoice → ℝ
  | .A => 49 / 100
  | .B => 33 / 100
  | .C => 14 / 100
  | .D => 84 / 100

/-- A displayed value is the nearest-hundredth readout of an exact magnification. -/
def IsNearestHundredthReadout (exact reported : ℝ) : Prop :=
  (∃ hundredths : ℤ, reported = (hundredths : ℝ) / 100) ∧
    |exact - reported| ≤ 1 / 200

/-!
The signed thin-lens equation with `f = -50 cm` and `s = 100 cm` determines
the virtual-image distance `s' = -100/3 cm`.
-/
lemma signedImageDistanceInCentimeters_eq_neg_hundred_div_three
    (setup : DivergingLensSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_signConvention : UsesCartesianSignConvention setup)
    (_physical : HasPhysicalSignConfiguration setup)
    (_thinLens : ObeysSignedThinLensEquation setup) :
    lengthInCentimeters setup.signedImageDistance = -(100 / 3) := by
  have hfocal :
      lengthInCentimeters setup.signedFocalLength = -50 := by
    rw [_signConvention.diverging_focal_length,
      _figure.focal_length_magnitude]
  have hlens := _thinLens centimeterUnitChoices
  have hlensVal := congrArg WithDim.val hlens
  change
    lengthInCentimeters setup.signedFocalLength *
          (lengthInCentimeters setup.objectDistance +
            lengthInCentimeters setup.signedImageDistance) =
        lengthInCentimeters setup.objectDistance *
          lengthInCentimeters setup.signedImageDistance at hlensVal
  rw [hfocal, _figure.object_distance] at hlensVal
  linarith

/-!
The transverse-magnification law and the derived virtual-image distance give
the exact upright magnification `m = 1/3`.
-/
lemma magnification_eq_one_third
    (setup : DivergingLensSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_signConvention : UsesCartesianSignConvention setup)
    (_physical : HasPhysicalSignConfiguration setup)
    (_thinLens : ObeysSignedThinLensEquation setup)
    (_magnificationLaw : ObeysTransverseMagnificationLaw setup) :
    setup.magnification = 1 / 3 := by
  have himage :=
    signedImageDistanceInCentimeters_eq_neg_hundred_div_three
      setup _figure _signConvention _physical _thinLens
  have hmagnification := _magnificationLaw.1 centimeterUnitChoices
  change
    setup.magnification =
      -lengthInCentimeters setup.signedImageDistance /
        lengthInCentimeters setup.objectDistance at hmagnification
  rw [himage, _figure.object_distance] at hmagnification
  norm_num at hmagnification ⊢
  exact hmagnification

/-!
The diverging lens produces exact magnification `1/3`; its nearest-hundredth
display is `0.33`, answer choice B.

This formalizes `thm:physics:phyx_mini_0053:target`.
-/
theorem problem_phyx_mini_0053
    (setup : DivergingLensSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_signConvention : UsesCartesianSignConvention setup)
    (_physical : HasPhysicalSignConfiguration setup)
    (_thinLens : ObeysSignedThinLensEquation setup)
    (_magnificationLaw : ObeysTransverseMagnificationLaw setup) :
    setup.magnification = 1 / 3 ∧
      IsNearestHundredthReadout
        setup.magnification AnswerChoice.B.magnification := by
  have hmagnification :=
    magnification_eq_one_third
      setup _figure _signConvention _physical _thinLens _magnificationLaw
  refine ⟨hmagnification, ?_⟩
  rw [hmagnification]
  constructor
  · refine ⟨33, ?_⟩
    norm_num [AnswerChoice.magnification]
  · norm_num [AnswerChoice.magnification, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0053
