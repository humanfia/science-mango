import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0044

open Dimension

/-!
# Contact-lens correction for a hyperopic eye

The unaided near point, desired object distance, signed thin-lens distances,
and focal length are dimensionful physical lengths.  Their scalar readouts are
expressed in centimeters to match the primary figure.  Under the Cartesian
sign convention used there, the real object has positive distance `s = 25 cm`
and the virtual image at the eye's unaided near point has signed distance
`s' = -100 cm`.
-/

/-- A signed physical length whose numerical value changes coherently with units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The two paraxial thin-lens types, distinguished physically by focal-length sign. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Whether the geometrical image is formed by actual rays or by their backward extensions. -/
inductive GeometricalImageKind where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The unaided eye datum relevant to the correction problem. -/
structure HyperopicEye where
  /-- Positive distance from the eye to its closest clearly visible object point. -/
  nearPointDistanceFromEye : LengthQuantity

/-- A thin contact lens and its signed focal length. -/
structure ThinContactLens where
  focalLength : LengthQuantity
  kind : ThinLensKind

/-!
The physical quantities and figure labels in the correction setup.

`desiredObjectDistanceFromEye` and the eye's near-point distance are positive
magnitudes measured in front of the eye. `objectDistanceFromLens` and
`signedImageDistanceFromLens` use the signed convention of the thin-lens
equation. The contact-lens approximation places the lens at the eye plane.
-/
structure ContactLensCorrectionSetup where
  eye : HyperopicEye
  lens : ThinContactLens
  desiredObjectDistanceFromEye : LengthQuantity
  objectDistanceFromLens : LengthQuantity
  signedImageDistanceFromLens : LengthQuantity
  imageKind : GeometricalImageKind

/-- Numerical distances stated in the problem text, before the eye-plane approximation. -/
structure MatchesScenarioReadouts (setup : ContactLensCorrectionSetup) : Prop where
  near_point_distance :
    lengthInCentimeters setup.eye.nearPointDistanceFromEye = 100
  desired_object_distance :
    lengthInCentimeters setup.desiredObjectDistanceFromEye = 25

/-!
Readouts and qualitative labels transcribed from the primary figure: the
contact lens is converging, `s = 25 cm`, and the backward ray extensions form
a virtual image at signed distance `s' = -100 cm`.
-/
structure MatchesPrimaryFigure (setup : ContactLensCorrectionSetup) : Prop where
  lens_is_converging : setup.lens.kind = .converging
  image_is_virtual : setup.imageKind = .virtual
  object_distance_label :
    lengthInCentimeters setup.objectDistanceFromLens = 25
  signed_image_distance_label :
    lengthInCentimeters setup.signedImageDistanceFromLens = -100

/-!
The contact lens is modeled at the eye plane, and it must make the desired
object appear at the unaided near point. The second equality implements the
Cartesian sign convention for an image on the object's side of the lens.
-/
structure UsesContactLensEyePlaneModel (setup : ContactLensCorrectionSetup) : Prop where
  object_distance_from_lens :
    lengthInCentimeters setup.objectDistanceFromLens =
      lengthInCentimeters setup.desiredObjectDistanceFromEye
  virtual_image_at_near_point :
    lengthInCentimeters setup.signedImageDistanceFromLens =
      -lengthInCentimeters setup.eye.nearPointDistanceFromEye

/-- The physical sign branch depicted for correcting near vision in a hyperopic eye. -/
structure HasDepictedSignConfiguration (setup : ContactLensCorrectionSetup) : Prop where
  desired_distance_positive :
    0 < lengthInCentimeters setup.desiredObjectDistanceFromEye
  desired_distance_inside_near_point :
    lengthInCentimeters setup.desiredObjectDistanceFromEye <
      lengthInCentimeters setup.eye.nearPointDistanceFromEye
  object_distance_positive :
    0 < lengthInCentimeters setup.objectDistanceFromLens
  image_distance_negative :
    lengthInCentimeters setup.signedImageDistanceFromLens < 0
  focal_length_positive :
    0 < lengthInCentimeters setup.lens.focalLength

/-!
The signed Gaussian thin-lens equation `1/f = 1/s + 1/s'`, written in the
single centimeter unit system used by the diagram.
-/
def SatisfiesSignedThinLensEquation (setup : ContactLensCorrectionSetup) : Prop :=
  1 / lengthInCentimeters setup.lens.focalLength =
    1 / lengthInCentimeters setup.objectDistanceFromLens +
      1 / lengthInCentimeters setup.signedImageDistanceFromLens

/-- The four focal-length readouts printed beside the answer choices, in centimeters. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displayed whole-centimeter focal length for each answer choice. -/
def answerFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => 35
  | .B => 33
  | .C => 37
  | .D => 43

/-- Agreement between an exact focal length and a displayed nearest-centimeter answer. -/
def MatchesAnswerToNearestCentimeter
    (focalLength : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters focalLength - answerFocalLengthInCentimeters choice| ≤ 1 / 2

/-!
The two signed distances in the primary figure make the reciprocal focal
length exactly `3/100 cm⁻¹` by the thin-lens equation.
-/
lemma reciprocalFocalLength_eq_three_hundredths
    (setup : ContactLensCorrectionSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_thinLens : SatisfiesSignedThinLensEquation setup) :
    1 / lengthInCentimeters setup.lens.focalLength = 3 / 100 := by
  calc
    1 / lengthInCentimeters setup.lens.focalLength =
        1 / lengthInCentimeters setup.objectDistanceFromLens +
          1 / lengthInCentimeters setup.signedImageDistanceFromLens := _thinLens
    _ = 3 / 100 := by
      rw [_figure.object_distance_label, _figure.signed_image_distance_label]
      norm_num

/-!
The corrective contact lens has exact focal length `100/3 cm`. Its
nearest-whole-centimeter readout is `33 cm`, answer choice B.

This formalizes `thm:physics:phyx_mini_0044:target`.
-/
theorem problem_phyx_mini_0044
    (setup : ContactLensCorrectionSetup)
    (_scenario : MatchesScenarioReadouts setup)
    (_figure : MatchesPrimaryFigure setup)
    (_eyePlane : UsesContactLensEyePlaneModel setup)
    (_physical : HasDepictedSignConfiguration setup)
    (_thinLens : SatisfiesSignedThinLensEquation setup) :
    lengthInCentimeters setup.lens.focalLength = 100 / 3 ∧
      MatchesAnswerToNearestCentimeter setup.lens.focalLength .B := by
  have hinv :=
    reciprocalFocalLength_eq_three_hundredths setup _figure _thinLens
  have hf_ne : lengthInCentimeters setup.lens.focalLength ≠ 0 :=
    ne_of_gt _physical.focal_length_positive
  have hf : lengthInCentimeters setup.lens.focalLength = 100 / 3 := by
    field_simp [hf_ne] at hinv
    linarith
  refine ⟨hf, ?_⟩
  norm_num [MatchesAnswerToNearestCentimeter, answerFocalLengthInCentimeters, hf]

end PhyXMiniProblems.ProblemPhyXMini0044
