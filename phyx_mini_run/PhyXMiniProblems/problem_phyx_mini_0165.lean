import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

/-!
# Effective focal length of a separated two-lens camera system

Light first meets a diverging lens of signed focal length `-120 mm` and then
a converging lens of focal length `42 mm`, whose centers are `60 mm` apart.
The object is `500 mm` before the first lens and has height `10 cm`.

All focal lengths, axial positions, object/image distances, and transverse
heights below are genuine Physlib dimensionful lengths. Real numbers occur
only as unit readouts and dimensionless comparisons. The signed Cartesian
convention makes the virtual intermediate-image distance `s₁'` negative.

The primary image confirms the diverging-then-converging ordering, the
`60 mm` separation, the labels `s₁`, `s₁'`, `s₂`, and `s₂'`, and a separate
`100 mm` scale bar. In particular, that scale-bar label is not an alternative
object distance.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0165

open Dimension

/-- A signed physical length, independent of the unit used to read it. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI unit choices with millimeters selected as the length unit. -/
def millimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.millimeters }

/-- The signed real-valued millimeter readout of a physical length. -/
def millimetersValue (length : OpticalLength) : ℝ :=
  (length millimeterUnitChoices).val

/-- The two camera lenses in the left-to-right order traversed by the light. -/
inductive LensLabel where
  | first
  | second
  deriving DecidableEq, Repr

/-- Qualitative kind of a paraxial thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- A camera lens with its figure label, optical kind, and signed focal length. -/
structure ThinLens where
  label : LensLabel
  kind : ThinLensKind
  signedFocalLength : OpticalLength

/--
The labeled points on the common principal axis of the source ray diagram.

The first lens forms `intermediateImageBase`; that image is the object used
by the second lens. The effective single lens is placed at
`effectiveLensCenter`, the midpoint of the two physical lens centers.
-/
inductive FigurePoint where
  | objectBase
  | intermediateImageBase
  | firstLensCenter
  | effectiveLensCenter
  | secondLensCenter
  | finalImageBase
  deriving DecidableEq, Repr

/-- The two physical imaging stages and the comparison lens at the midpoint. -/
inductive ImagingStage where
  | firstLens
  | secondLens
  | effectiveMidpointLens
  deriving DecidableEq, Repr

/-!
The physical quantities in the camera problem and its ray diagram.

The four signed-distance fields retain the printed labels `s₁`, `s₁'`, `s₂`,
and `s₂'`. The equivalent-lens distances are measured from the midpoint lens
to the same object and final image. `effectiveFocalLength` is an unknown
physical length: no numerical answer is built into this structure.
-/
structure TwoLensCameraSetup where
  lens : LensLabel → ThinLens
  axisPosition : FigurePoint → OpticalLength
  lensSeparation : OpticalLength
  objectHeight : OpticalLength
  figureScaleBarLength : OpticalLength
  objectDistanceFirst : OpticalLength
  signedIntermediateImageDistanceFirst : OpticalLength
  objectDistanceSecond : OpticalLength
  signedFinalImageDistanceSecond : OpticalLength
  effectiveObjectDistance : OpticalLength
  effectiveImageDistance : OpticalLength
  effectiveFocalLength : OpticalLength

/-- The focal length used at each of the three imaging stages. -/
def stageFocalLength
    (setup : TwoLensCameraSetup) : ImagingStage → OpticalLength
  | .firstLens => (setup.lens .first).signedFocalLength
  | .secondLens => (setup.lens .second).signedFocalLength
  | .effectiveMidpointLens => setup.effectiveFocalLength

/-- The signed Cartesian object distance used at an imaging stage. -/
def stageObjectDistance
    (setup : TwoLensCameraSetup) : ImagingStage → OpticalLength
  | .firstLens => setup.objectDistanceFirst
  | .secondLens => setup.objectDistanceSecond
  | .effectiveMidpointLens => setup.effectiveObjectDistance

/-- The signed Cartesian image distance produced at an imaging stage. -/
def stageImageDistance
    (setup : TwoLensCameraSetup) : ImagingStage → OpticalLength
  | .firstLens => setup.signedIntermediateImageDistanceFirst
  | .secondLens => setup.signedFinalImageDistanceSecond
  | .effectiveMidpointLens => setup.effectiveImageDistance

/-!
Problem and primary-figure readouts. The `10 cm` object height is recorded as
the equivalent `100 mm` length so that all numerical data share one unit.
Neither an image distance nor the requested effective focal length is fixed.
-/
structure HasStatedCameraData (setup : TwoLensCameraSetup) : Prop where
  first_lens_label : (setup.lens .first).label = .first
  second_lens_label : (setup.lens .second).label = .second
  first_lens_diverging : (setup.lens .first).kind = .diverging
  second_lens_converging : (setup.lens .second).kind = .converging
  first_focal_length_millimeters :
    millimetersValue (setup.lens .first).signedFocalLength = -120
  second_focal_length_millimeters :
    millimetersValue (setup.lens .second).signedFocalLength = 42
  lens_separation_millimeters : millimetersValue setup.lensSeparation = 60
  object_distance_millimeters : millimetersValue setup.objectDistanceFirst = 500
  object_height_millimeters : millimetersValue setup.objectHeight = 100
  figure_scale_bar_millimeters :
    millimetersValue setup.figureScaleBarLength = 100

/-!
Axis geometry read from the ray diagram and from the definition of the
effective lens. It relates each labeled signed distance to the corresponding
pair of points in every unit system, and puts the comparison lens exactly at
the midpoint. It does not prescribe any image location numerically.
-/
def HasLabeledAxisGeometry (setup : TwoLensCameraSetup) : Prop :=
  ∀ units : UnitChoices,
    (setup.lensSeparation units).val =
        (setup.axisPosition .secondLensCenter units).val -
          (setup.axisPosition .firstLensCenter units).val ∧
      (setup.objectDistanceFirst units).val =
        (setup.axisPosition .firstLensCenter units).val -
          (setup.axisPosition .objectBase units).val ∧
      (setup.signedIntermediateImageDistanceFirst units).val =
        (setup.axisPosition .intermediateImageBase units).val -
          (setup.axisPosition .firstLensCenter units).val ∧
      (setup.objectDistanceSecond units).val =
        (setup.axisPosition .secondLensCenter units).val -
          (setup.axisPosition .intermediateImageBase units).val ∧
      (setup.signedFinalImageDistanceSecond units).val =
        (setup.axisPosition .finalImageBase units).val -
          (setup.axisPosition .secondLensCenter units).val ∧
      (setup.effectiveObjectDistance units).val =
        (setup.axisPosition .effectiveLensCenter units).val -
          (setup.axisPosition .objectBase units).val ∧
      (setup.effectiveImageDistance units).val =
        (setup.axisPosition .finalImageBase units).val -
          (setup.axisPosition .effectiveLensCenter units).val ∧
      2 * (setup.axisPosition .effectiveLensCenter units).val =
        (setup.axisPosition .firstLensCenter units).val +
          (setup.axisPosition .secondLensCenter units).val

/-!
Qualitative ray-diagram information: the object is on the incoming side, the
first diverging lens makes a virtual intermediate image on its left, and the
second lens makes the final real image on its right. These are order/sign
conditions only, not the requested focal-length value.
-/
structure MatchesPrimaryRayDiagram (setup : TwoLensCameraSetup) : Prop where
  labeled_axis_geometry : HasLabeledAxisGeometry setup
  object_before_first_lens :
    millimetersValue (setup.axisPosition .objectBase) <
      millimetersValue (setup.axisPosition .firstLensCenter)
  virtual_intermediate_image_left_of_first_lens :
    millimetersValue (setup.axisPosition .intermediateImageBase) <
      millimetersValue (setup.axisPosition .firstLensCenter)
  first_lens_before_second_lens :
    millimetersValue (setup.axisPosition .firstLensCenter) <
      millimetersValue (setup.axisPosition .secondLensCenter)
  real_final_image_right_of_second_lens :
    millimetersValue (setup.axisPosition .secondLensCenter) <
      millimetersValue (setup.axisPosition .finalImageBase)

/-- Nondegeneracy and sign conditions for the pictured physical configuration. -/
structure HasPhysicalSignConfiguration (setup : TwoLensCameraSetup) : Prop where
  object_height_positive : 0 < millimetersValue setup.objectHeight
  lens_separation_positive : 0 < millimetersValue setup.lensSeparation
  first_focal_length_negative :
    millimetersValue (setup.lens .first).signedFocalLength < 0
  second_focal_length_positive :
    0 < millimetersValue (setup.lens .second).signedFocalLength
  first_object_distance_positive : 0 < millimetersValue setup.objectDistanceFirst
  first_image_distance_negative :
    millimetersValue setup.signedIntermediateImageDistanceFirst < 0
  second_object_distance_positive : 0 < millimetersValue setup.objectDistanceSecond
  second_image_distance_positive :
    0 < millimetersValue setup.signedFinalImageDistanceSecond
  effective_object_distance_positive :
    0 < millimetersValue setup.effectiveObjectDistance
  effective_image_distance_positive :
    0 < millimetersValue setup.effectiveImageDistance

/-!
The signed Gaussian thin-lens equation `1/f = 1/s + 1/s'`, written in the
division-free, dimensionally homogeneous form `f (s + s') = s s'` and
required in every unit system. At `.effectiveMidpointLens` this is precisely
the problem's definition of the comparison focal length: a single midpoint
lens forms the final image at the same location.
-/
def ObeysSignedThinLensEquationAt
    (setup : TwoLensCameraSetup) (stage : ImagingStage) : Prop :=
  ∀ units : UnitChoices,
    stageFocalLength setup stage units *
        (stageObjectDistance setup stage units +
          stageImageDistance setup stage units) =
      stageObjectDistance setup stage units *
        stageImageDistance setup stage units

/-- Labels of the four multiple-choice answers in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The focal-length readout, in millimeters, printed beside an answer choice. -/
def AnswerChoice.focalLengthMillimeters : AnswerChoice → ℝ
  | .A => 50
  | .B => 75
  | .C => 100
  | .D => 125

/-- Dataset metadata only: the source records answer choice B. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- Agreement with an answer choice to the nearest millimeter. -/
def MatchesDisplayedFocalLength
    (setup : TwoLensCameraSetup) (choice : AnswerChoice) : Prop :=
  |millimetersValue setup.effectiveFocalLength -
      choice.focalLengthMillimeters| ≤ 1 / 2

/-- A choice is correct when its displayed value is nearest to the exact focal length. -/
def IsNearestDisplayedChoice
    (setup : TwoLensCameraSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |millimetersValue setup.effectiveFocalLength -
        choice.focalLengthMillimeters| ≤
      |millimetersValue setup.effectiveFocalLength -
        other.focalLengthMillimeters|

/-!
The first two signed thin-lens equations and the sequential axis geometry
determine the virtual intermediate image, the second object distance, and the
final image made by the converging lens.
-/
lemma sequentialDistancesInMillimeters_eq
    (setup : TwoLensCameraSetup)
    (h_data : HasStatedCameraData setup)
    (h_figure : MatchesPrimaryRayDiagram setup)
    (h_physical : HasPhysicalSignConfiguration setup)
    (h_first_lens : ObeysSignedThinLensEquationAt setup .firstLens)
    (h_second_lens : ObeysSignedThinLensEquationAt setup .secondLens) :
    millimetersValue setup.signedIntermediateImageDistanceFirst = -(3000 / 31) ∧
      millimetersValue setup.objectDistanceSecond = 4860 / 31 ∧
      millimetersValue setup.signedFinalImageDistanceSecond = 34020 / 593 := by
  sorry

/-!
Because the comparison lens is at the midpoint, its object distance is
`530 mm` and its image distance is `51810/593 mm`; both are derived from the
same object and final-image points, not supplied as answer data.
-/
lemma effectiveDistancesInMillimeters_eq
    (setup : TwoLensCameraSetup)
    (h_data : HasStatedCameraData setup)
    (h_figure : MatchesPrimaryRayDiagram setup)
    (h_physical : HasPhysicalSignConfiguration setup)
    (h_first_lens : ObeysSignedThinLensEquationAt setup .firstLens)
    (h_second_lens : ObeysSignedThinLensEquationAt setup .secondLens) :
    millimetersValue setup.effectiveObjectDistance = 530 ∧
      millimetersValue setup.effectiveImageDistance = 51810 / 593 := by
  sorry

/-!
The midpoint comparison lens has exact focal length `274593/3661 mm`, about
`75.0049 mm`. Thus its nearest-millimeter value is `75 mm`, answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0165:target`.
-/
theorem problem_phyx_mini_0165
    (setup : TwoLensCameraSetup)
    (h_data : HasStatedCameraData setup)
    (h_figure : MatchesPrimaryRayDiagram setup)
    (h_physical : HasPhysicalSignConfiguration setup)
    (h_lens_laws : ∀ stage, ObeysSignedThinLensEquationAt setup stage) :
    millimetersValue setup.effectiveFocalLength = 274593 / 3661 ∧
      MatchesDisplayedFocalLength setup .B ∧
      IsNearestDisplayedChoice setup .B := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0165
