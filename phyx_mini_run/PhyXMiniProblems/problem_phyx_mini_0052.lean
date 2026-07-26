import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0052

open Dimension

/-!
# Magnification produced by a hand magnifying glass

The magnifying glass is modeled as a converging paraxial thin lens. All axial
positions, focal lengths, and object/image distances are signed physical
lengths. The Cartesian convention takes a virtual image on the flower's side
of the lens to have negative image distance. Transverse magnification is a
dimensionless real number.

The supplied ray diagram places the lens at the origin, the flower `4 cm` to
its left, the focal points `6 cm` on either side, and an upright virtual image
`12 cm` to the left. The image location is declared below as a derived
consistency statement; it is not assumed by the main magnification theorem.
-/

/-- A signed physical length, independent of the unit used to read it. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices in which the length coordinate is read in centimeters. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed real-valued centimeter readout of a physical length. -/
def centimetersValue (length : OpticalLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- The lens type identified by the convex profile in the ray diagram. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Whether the rays themselves meet at the image or only their backward extensions do. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- Orientation of the image arrow relative to the flower/object arrow. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/--
The physical quantities and labels in the magnifying-glass ray diagram.

`objectDistanceFromLens` is positive for the flower on the incoming side,
whereas `signedImageDistanceFromLens` is negative for the virtual image in
this problem. The two focal-point positions and the object/image positions
retain the geometry shown on the principal axis.
-/
structure MagnifyingGlassDiagram where
  lensKind : ThinLensKind
  lensAxialPosition : OpticalLength
  flowerAxialPosition : OpticalLength
  leftFocalPointPosition : OpticalLength
  rightFocalPointPosition : OpticalLength
  imageAxialPosition : OpticalLength
  focalLength : OpticalLength
  objectDistanceFromLens : OpticalLength
  signedImageDistanceFromLens : OpticalLength
  transverseMagnification : ℝ
  imageNature : ImageNature
  imageOrientation : ImageOrientation

/--
Problem data: a converging magnifying glass of focal length `6.0 cm` is held
`4.0 cm` from the flower.
-/
def HasStatedProblemData (diagram : MagnifyingGlassDiagram) : Prop :=
  diagram.lensKind = .converging ∧
    centimetersValue diagram.focalLength = 6 ∧
    centimetersValue diagram.objectDistanceFromLens = 4

/-- The stated focal length and flower-to-lens distance are physical positive lengths. -/
def HasPositiveProblemLengths (diagram : MagnifyingGlassDiagram) : Prop :=
  0 < centimetersValue diagram.focalLength ∧
    0 < centimetersValue diagram.objectDistanceFromLens

/--
Geometry and qualitative labels read from the ray diagram. The numerical
image location is deliberately absent: the dashed rays identify the image as
virtual and upright, but its `-12 cm` signed distance is derived from the lens
law below.
-/
def MatchesRayDiagram (diagram : MagnifyingGlassDiagram) : Prop :=
  centimetersValue diagram.lensAxialPosition = 0 ∧
    centimetersValue diagram.flowerAxialPosition = -4 ∧
    centimetersValue diagram.leftFocalPointPosition = -6 ∧
    centimetersValue diagram.rightFocalPointPosition = 6 ∧
    (∀ units : UnitChoices,
      diagram.objectDistanceFromLens units =
        diagram.lensAxialPosition units - diagram.flowerAxialPosition units) ∧
    (∀ units : UnitChoices,
      diagram.signedImageDistanceFromLens units =
        diagram.imageAxialPosition units - diagram.lensAxialPosition units) ∧
    diagram.imageNature = .virtual ∧
    diagram.imageOrientation = .upright

/--
The Cartesian sign convention used in the figure: a virtual image has
negative signed image distance, and an upright image has positive
magnification.
-/
def UsesCartesianSignConvention (diagram : MagnifyingGlassDiagram) : Prop :=
  (diagram.imageNature = .virtual ↔
      centimetersValue diagram.signedImageDistanceFromLens < 0) ∧
    (diagram.imageOrientation = .upright ↔
      0 < diagram.transverseMagnification)

/--
The paraxial thin-lens equation `1/f = 1/s + 1/s'`, written in the
division-free, dimensionally homogeneous form `f * (s + s') = s * s'`.
Requiring it for every unit choice makes the governing law independent of the
centimeter readout used for the numerical data.
-/
def ObeysThinLensEquation (diagram : MagnifyingGlassDiagram) : Prop :=
  ∀ units : UnitChoices,
    diagram.focalLength units *
        (diagram.objectDistanceFromLens units +
          diagram.signedImageDistanceFromLens units) =
      diagram.objectDistanceFromLens units *
        diagram.signedImageDistanceFromLens units

/-- The signed transverse-magnification law `m = -s'/s`. -/
def ObeysTransverseMagnificationLaw (diagram : MagnifyingGlassDiagram) : Prop :=
  ∀ units : UnitChoices,
    diagram.transverseMagnification =
      - (diagram.signedImageDistanceFromLens units).val /
        (diagram.objectDistanceFromLens units).val

/--
The numerical image-location annotation visible in the auxiliary ray diagram.
This is a consistency property to be derived, not a premise of the target.
-/
def HasDisplayedImageLocation (diagram : MagnifyingGlassDiagram) : Prop :=
  centimetersValue diagram.imageAxialPosition = -12 ∧
    centimetersValue diagram.signedImageDistanceFromLens = -12

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless magnification printed beside each answer choice. -/
def answerMagnification : AnswerChoice → ℝ
  | .A => 32 / 5
  | .B => 3
  | .C => 89 / 10
  | .D => 31 / 25

/-- A choice is correct precisely when its printed value equals the physical magnification. -/
def IsCorrectAnswer (diagram : MagnifyingGlassDiagram) (choice : AnswerChoice) : Prop :=
  answerMagnification choice = diagram.transverseMagnification

/--
The thin-lens law and the two stated distances determine the virtual-image
distance `s' = -12 cm`; this also matches the image label in the ray diagram.
-/
lemma signedImageDistance_eq_neg_twelve
    (diagram : MagnifyingGlassDiagram)
    (h_data : HasStatedProblemData diagram)
    (h_lens : ObeysThinLensEquation diagram) :
    centimetersValue diagram.signedImageDistanceFromLens = -12 := by
  rcases h_data with ⟨_, hf, hs⟩
  have h_lens_cm := h_lens centimeterUnitChoices
  have h_lens_val := congrArg (fun x => x.val) h_lens_cm
  change
    centimetersValue diagram.focalLength *
        (centimetersValue diagram.objectDistanceFromLens +
          centimetersValue diagram.signedImageDistanceFromLens) =
      centimetersValue diagram.objectDistanceFromLens *
        centimetersValue diagram.signedImageDistanceFromLens at h_lens_val
  nlinarith

/--
The problem data, thin-lens equation, and labeled axis geometry reproduce the
auxiliary diagram's image position `12 cm` to the left of the lens.
-/
lemma displayedImageLocation_follows
    (diagram : MagnifyingGlassDiagram)
    (h_data : HasStatedProblemData diagram)
    (h_figure : MatchesRayDiagram diagram)
    (h_lens : ObeysThinLensEquation diagram) :
    HasDisplayedImageLocation diagram := by
  have h_signed := signedImageDistance_eq_neg_twelve diagram h_data h_lens
  rcases h_figure with ⟨h_lens_pos, _, _, _, _, h_image_geometry, _, _⟩
  have h_image_geometry_cm :=
    congrArg (fun x => x.val) (h_image_geometry centimeterUnitChoices)
  change
    centimetersValue diagram.signedImageDistanceFromLens =
      centimetersValue diagram.imageAxialPosition -
        centimetersValue diagram.lensAxialPosition at h_image_geometry_cm
  unfold HasDisplayedImageLocation
  constructor
  · nlinarith
  · exact h_signed

/--
A `6.0 cm` converging thin lens held `4.0 cm` from the flower has signed image
distance `-12 cm`, so `m = -s'/s = 3.0`. Hence the correct answer is B.

This formalizes `thm:physics:phyx_mini_0052:target`.
-/
theorem problem_phyx_mini_0052
    (diagram : MagnifyingGlassDiagram)
    (h_data : HasStatedProblemData diagram)
    (h_positive : HasPositiveProblemLengths diagram)
    (h_figure : MatchesRayDiagram diagram)
    (h_sign : UsesCartesianSignConvention diagram)
    (h_lens : ObeysThinLensEquation diagram)
    (h_magnification : ObeysTransverseMagnificationLaw diagram) :
    diagram.transverseMagnification = 3 ∧
      IsCorrectAnswer diagram .B := by
  have h_signed := signedImageDistance_eq_neg_twelve diagram h_data h_lens
  rcases h_data with ⟨_, _, h_object⟩
  have h_magnification_cm := h_magnification centimeterUnitChoices
  change
    diagram.transverseMagnification =
      - centimetersValue diagram.signedImageDistanceFromLens /
        centimetersValue diagram.objectDistanceFromLens at h_magnification_cm
  rw [h_signed, h_object] at h_magnification_cm
  norm_num at h_magnification_cm
  exact ⟨h_magnification_cm, by
    simpa [IsCorrectAnswer, answerMagnification] using h_magnification_cm.symm⟩

end PhyXMiniProblems.ProblemPhyXMini0052
