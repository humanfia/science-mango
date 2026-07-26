import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0159

open Dimension

/-!
# Diameter of the camera image of a flower

The camera is modeled by a converging paraxial thin lens.  Focal length,
axial positions, object and image distances, the optical-axis scale interval,
and transverse diameters are physical lengths.  Scalar data from the problem
and figure are read in centimeters.

The image diagram is instructional.  In particular, its `25 cm` brace labels
one interval of the drawn optical-axis scale; the stated flower-to-lens
distance is the separate dimension line labeled `s = 200 cm`.
-/

/-- A signed physical length whose scalar representation depends coherently on units. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of an optical length in centimeters. -/
def lengthInCentimeters (length : OpticalLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- The optical power sign represented by the profile of a thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Whether the refracted rays themselves meet at the image. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- Transverse orientation of the image relative to the object. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- Orientation of the principal optical axis in the source figure. -/
inductive PrincipalAxisOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Labeled axial points in the ray-tracing diagram. -/
inductive FigurePoint where
  | objectBase
  | leftFocalPoint
  | lensCenter
  | rightFocalPoint
  | imageBase
  deriving DecidableEq, Repr

/-- Labels of the three special rays named in step 4 of the figure. -/
inductive FigureRay where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The standard geometrical-optics role assigned to a special ray. -/
inductive PrincipalRayRole where
  | parallelThenThroughFarFocus
  | throughNearFocusThenParallel
  | undeviatedThroughLensCenter
  deriving DecidableEq, Repr

/-- The two occurrences of the angle label `θ` on the central ray. -/
inductive FigureAngleMark where
  | incident
  | transmitted
  deriving DecidableEq, Repr

/-!
The physical quantities and figure labels in the camera setup.

The object and image diameters are positive transverse magnitudes.  Axial
positions are signed.  `objectDistance` and `imageDistance` are positive
distance magnitudes for the pictured real-image configuration.  The marked
angles are dimensionless real readouts in radians.
-/
structure CameraLensSetup where
  lensKind : ThinLensKind
  imageNature : ImageNature
  imageOrientation : ImageOrientation
  principalAxisOrientation : PrincipalAxisOrientation
  focalLength : OpticalLength
  objectDistance : OpticalLength
  imageDistance : OpticalLength
  objectDiameter : OpticalLength
  imageDiameter : OpticalLength
  axisScaleInterval : OpticalLength
  axisPosition : FigurePoint → OpticalLength
  rayRole : FigureRay → PrincipalRayRole
  rayIsDrawn : FigureRay → Prop
  markedAngleRadians : FigureAngleMark → ℝ

/-!
Problem-statement data.  These are the three input measurements: flower
diameter `4.0 cm`, object distance `200 cm`, and focal length `50 cm`.
No image distance or image diameter is specified here.
-/
structure HasStatedCameraData (setup : CameraLensSetup) : Prop where
  lens_is_converging : setup.lensKind = .converging
  flower_diameter_cm : lengthInCentimeters setup.objectDiameter = 4
  object_distance_cm : lengthInCentimeters setup.objectDistance = 200
  focal_length_cm : lengthInCentimeters setup.focalLength = 50

/-!
Readouts and qualitative geometry taken from the primary figure.  The lens is
at the origin; the object and focal points agree with the stated scale; and
the real, inverted image lies beyond the far focal point.  Its exact position
and diameter remain deliberately unspecified.
-/
structure MatchesPrimaryFigure (setup : CameraLensSetup) : Prop where
  axis_is_horizontal : setup.principalAxisOrientation = .horizontal
  image_is_real : setup.imageNature = .real
  image_is_inverted : setup.imageOrientation = .inverted
  lens_center_at_origin :
    lengthInCentimeters (setup.axisPosition .lensCenter) = 0
  object_position_cm :
    lengthInCentimeters (setup.axisPosition .objectBase) = -200
  left_focal_position_cm :
    lengthInCentimeters (setup.axisPosition .leftFocalPoint) = -50
  right_focal_position_cm :
    lengthInCentimeters (setup.axisPosition .rightFocalPoint) = 50
  scale_interval_cm : lengthInCentimeters setup.axisScaleInterval = 25
  image_beyond_right_focus :
    lengthInCentimeters (setup.axisPosition .rightFocalPoint) <
      lengthInCentimeters (setup.axisPosition .imageBase)
  ray_a_role : setup.rayRole .a = .parallelThenThroughFarFocus
  ray_b_role : setup.rayRole .b = .throughNearFocusThenParallel
  ray_c_role : setup.rayRole .c = .undeviatedThroughLensCenter
  ray_a_is_drawn : setup.rayIsDrawn .a
  ray_b_is_drawn : setup.rayIsDrawn .b
  ray_c_is_drawn : setup.rayIsDrawn .c
  theta_marks_agree :
    setup.markedAngleRadians .incident = setup.markedAngleRadians .transmitted

/-!
Axial-distance bookkeeping for the sign convention shown in the figure.
The incoming object and outgoing real image both have positive distance
magnitudes, while the axial coordinates themselves are signed.
-/
structure UsesRealImageDistanceConvention (setup : CameraLensSetup) : Prop where
  object_distance_from_positions :
    ∀ units : UnitChoices,
      setup.objectDistance units =
        setup.axisPosition .lensCenter units -
          setup.axisPosition .objectBase units
  image_distance_from_positions :
    ∀ units : UnitChoices,
      setup.imageDistance units =
        setup.axisPosition .imageBase units -
          setup.axisPosition .lensCenter units
  right_focus_from_focal_length :
    ∀ units : UnitChoices,
      setup.focalLength units =
        setup.axisPosition .rightFocalPoint units -
          setup.axisPosition .lensCenter units
  left_focus_from_focal_length :
    ∀ units : UnitChoices,
      setup.focalLength units =
        setup.axisPosition .lensCenter units -
          setup.axisPosition .leftFocalPoint units

/-- Positivity conditions for the physical magnitudes in this real-image setup. -/
structure HasPhysicalLengthConfiguration (setup : CameraLensSetup) : Prop where
  focal_length_positive : 0 < lengthInCentimeters setup.focalLength
  object_distance_positive : 0 < lengthInCentimeters setup.objectDistance
  image_distance_positive : 0 < lengthInCentimeters setup.imageDistance
  object_diameter_positive : 0 < lengthInCentimeters setup.objectDiameter
  image_diameter_positive : 0 < lengthInCentimeters setup.imageDiameter
  scale_interval_positive : 0 < lengthInCentimeters setup.axisScaleInterval

/-!
The Gaussian thin-lens equation `1/f = 1/s + 1/s'`, written without division
as `f (s + s') = s s'`.  It is required in every unit system, so this is a
law about dimensionful lengths rather than an equation about centimeter
placeholders.
-/
def ObeysGaussianThinLensEquation (setup : CameraLensSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.focalLength units *
        (setup.objectDistance units + setup.imageDistance units) =
      setup.objectDistance units * setup.imageDistance units

/-!
The magnitude form of transverse magnification,
`image diameter / object diameter = image distance / object distance`,
written homogeneously without division.  Image inversion is recorded
separately by `imageOrientation`; diameters themselves are nonnegative
magnitudes.
-/
def ObeysTransverseDiameterLaw (setup : CameraLensSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.imageDiameter units * setup.objectDistance units =
      setup.objectDiameter units * setup.imageDistance units

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The image-diameter readout in centimeters printed beside each choice. -/
def AnswerChoice.diameterInCentimeters : AnswerChoice → ℝ
  | .A => 15 / 10
  | .B => 13 / 10
  | .C => 17 / 10
  | .D => 19 / 10

/-- `reported` is a one-decimal-place readout within half a tenth of `exact`. -/
def IsNearestTenthReadout (exact reported : ℝ) : Prop :=
  (∃ tenths : ℤ, reported = (tenths : ℝ) / 10) ∧
    |exact - reported| ≤ 1 / 20

/-- A choice correctly reports the physical image diameter to the displayed precision. -/
def IsCorrectRoundedAnswer (setup : CameraLensSetup) (choice : AnswerChoice) : Prop :=
  IsNearestTenthReadout
    (lengthInCentimeters setup.imageDiameter)
    choice.diameterInCentimeters

/-!
The thin-lens equation with `f = 50 cm` and `s = 200 cm` determines the real
image distance `s' = 200/3 cm`.
-/
lemma imageDistanceInCentimeters_eq_two_hundred_div_three
    (setup : CameraLensSetup)
    (_data : HasStatedCameraData setup)
    (_physical : HasPhysicalLengthConfiguration setup)
    (_thinLens : ObeysGaussianThinLensEquation setup) :
    lengthInCentimeters setup.imageDistance = 200 / 3 := by
  have h := congrArg WithDim.val (_thinLens centimeterUnitChoices)
  change lengthInCentimeters setup.focalLength *
      (lengthInCentimeters setup.objectDistance +
        lengthInCentimeters setup.imageDistance) =
    lengthInCentimeters setup.objectDistance *
      lengthInCentimeters setup.imageDistance at h
  rw [_data.focal_length_cm, _data.object_distance_cm] at h
  norm_num at h ⊢
  linarith

/-!
The transverse-diameter law then gives the exact detector-image diameter
`4/3 cm` from the `4 cm` flower diameter.
-/
lemma imageDiameterInCentimeters_eq_four_div_three
    (setup : CameraLensSetup)
    (_data : HasStatedCameraData setup)
    (_physical : HasPhysicalLengthConfiguration setup)
    (_thinLens : ObeysGaussianThinLensEquation setup)
    (_transverse : ObeysTransverseDiameterLaw setup) :
    lengthInCentimeters setup.imageDiameter = 4 / 3 := by
  have hDist := imageDistanceInCentimeters_eq_two_hundred_div_three
    setup _data _physical _thinLens
  have h := congrArg WithDim.val (_transverse centimeterUnitChoices)
  change lengthInCentimeters setup.imageDiameter *
      lengthInCentimeters setup.objectDistance =
    lengthInCentimeters setup.objectDiameter *
      lengthInCentimeters setup.imageDistance at h
  rw [_data.object_distance_cm, _data.flower_diameter_cm, hDist] at h
  norm_num at h ⊢
  linarith

/-!
A `4.0 cm` flower at `200 cm` from a `50 cm` converging lens forms an exact
`4/3 cm`-diameter detector image.  To the one-decimal precision of the answer
choices this is `1.3 cm`, choice B.

This formalizes `thm:physics:phyx_mini_0159:target`.
-/
theorem problem_phyx_mini_0159
    (setup : CameraLensSetup)
    (_data : HasStatedCameraData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_signConvention : UsesRealImageDistanceConvention setup)
    (_physical : HasPhysicalLengthConfiguration setup)
    (_thinLens : ObeysGaussianThinLensEquation setup)
    (_transverse : ObeysTransverseDiameterLaw setup) :
    lengthInCentimeters setup.imageDiameter = 4 / 3 ∧
      IsCorrectRoundedAnswer setup .B := by
  have hDiameter := imageDiameterInCentimeters_eq_four_div_three
    setup _data _physical _thinLens _transverse
  constructor
  · exact hDiameter
  · unfold IsCorrectRoundedAnswer IsNearestTenthReadout
    rw [hDiameter]
    constructor
    · refine ⟨13, ?_⟩
      norm_num [AnswerChoice.diameterInCentimeters]
    · norm_num [AnswerChoice.diameterInCentimeters, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0159
