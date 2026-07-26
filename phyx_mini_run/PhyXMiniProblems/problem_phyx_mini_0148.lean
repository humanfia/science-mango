import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0148

open Dimension

/-!
# Focal length of the diverging lens in a two-lens system

The optical axis is oriented from left to right. A small upright object is
`25.0 cm` to the left of a diverging lens. A converging lens of focal length
`12.0 cm` is `30.0 cm` to the right of the diverging lens, and the system forms
a real inverted image `17.0 cm` to the right of the converging lens.

Axial positions and signed focal lengths are Physlib dimensionful lengths.
Ordinary real numbers occur only after centimeters have explicitly been chosen
as a readout unit. The unpictured intermediate image is represented as a
distinguished axial point: it is the image made by the first lens and the
object used by the second lens.
-/

/-- A signed physical length, independent of the unit chosen to read it. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The signed scalar readout of an axial position or focal length in centimeters. -/
def signedLengthInCentimeters (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := LengthUnit.centimeters}).val

/-- Labels for the two lenses, in their left-to-right order. -/
inductive LensLabel where
  | firstLens
  | secondLens
  deriving DecidableEq, Repr

/-- The optical classification of a thin lens. -/
inductive ThinLensKind where
  | diverging
  | converging
  deriving DecidableEq, Repr

/-- Named points on the common principal axis, including the derived conjugate. -/
inductive OpticalAxisPoint where
  | object
  | firstLensCenter
  | intermediateImage
  | secondLensCenter
  | finalImage
  deriving DecidableEq, Repr

/-- Direction in which light propagates through the pictured system. -/
inductive AxialPropagationDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-- The approximation regime under which the Gaussian thin-lens law is used. -/
inductive OpticalApproximation where
  | exactRayTracing
  | thinParaxial
  deriving DecidableEq, Repr

/-- The qualitative size regime assigned to the source object. -/
inductive ObjectSizeRegime where
  | small
  | extended
  deriving DecidableEq, Repr

/-- Whether an optical image is real or virtual. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- Transverse orientation of the object or image arrow. -/
inductive TransverseOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- A labeled thin lens with its center and signed physical focal length. -/
structure ThinLens where
  label : LensLabel
  kind : ThinLensKind
  center : OpticalAxisPoint
  signedFocalLength : SignedLengthQuantity

/-
The physical quantities and qualitative labels of the two-lens setup. The
position of `intermediateImage` is deliberately an unknown model quantity; it
is constrained only by the two governing lens equations below.
-/
structure TwoLensImagingSetup where
  lens : LensLabel → ThinLens
  axialPosition : OpticalAxisPoint → SignedLengthQuantity
  propagationDirection : AxialPropagationDirection
  approximation : OpticalApproximation
  objectSizeRegime : ObjectSizeRegime
  objectOrientation : TransverseOrientation
  finalImageNature : ImageNature
  finalImageOrientation : TransverseOrientation
  showsPrincipalAxis : Bool

/-- Centimeter coordinate of a named point on the optical axis. -/
def axialPositionInCentimeters
    (setup : TwoLensImagingSetup) (point : OpticalAxisPoint) : ℝ :=
  signedLengthInCentimeters (setup.axialPosition point)

/-- Signed focal-length readout of a lens in centimeters. -/
def focalLengthInCentimeters (lens : ThinLens) : ℝ :=
  signedLengthInCentimeters lens.signedFocalLength

/-- Positive object distance presented to the first lens. -/
def firstLensObjectDistanceInCentimeters (setup : TwoLensImagingSetup) : ℝ :=
  axialPositionInCentimeters setup .firstLensCenter -
    axialPositionInCentimeters setup .object

/-- Signed image distance made by the first lens. -/
def firstLensImageDistanceInCentimeters (setup : TwoLensImagingSetup) : ℝ :=
  axialPositionInCentimeters setup .intermediateImage -
    axialPositionInCentimeters setup .firstLensCenter

/-- Object distance presented by the shared intermediate image to the second lens. -/
def secondLensObjectDistanceInCentimeters (setup : TwoLensImagingSetup) : ℝ :=
  axialPositionInCentimeters setup .secondLensCenter -
    axialPositionInCentimeters setup .intermediateImage

/-- Signed distance from the second lens to the final image. -/
def secondLensImageDistanceInCentimeters (setup : TwoLensImagingSetup) : ℝ :=
  axialPositionInCentimeters setup .finalImage -
    axialPositionInCentimeters setup .secondLensCenter

/-- The Gaussian sign of a focal length agrees with its lens classification. -/
def HasFocalSignConsistentWithKind (lens : ThinLens) : Prop :=
  match lens.kind with
  | .diverging => focalLengthInCentimeters lens < 0
  | .converging => 0 < focalLengthInCentimeters lens

/-
Qualitative physical conditions needed for the signed paraxial model. These
fix the propagation direction, approximation, ordering of visible objects,
and focal-length signs, but do not assign a numerical focal length to the
first lens or a numerical position to the intermediate image.
-/
def HasPhysicalTwoLensConfiguration (setup : TwoLensImagingSetup) : Prop :=
  setup.propagationDirection = .leftToRight ∧
    setup.approximation = .thinParaxial ∧
    (setup.lens .firstLens).label = .firstLens ∧
    (setup.lens .secondLens).label = .secondLens ∧
    (setup.lens .firstLens).kind = .diverging ∧
    (setup.lens .secondLens).kind = .converging ∧
    (setup.lens .firstLens).center = .firstLensCenter ∧
    (setup.lens .secondLens).center = .secondLensCenter ∧
    HasFocalSignConsistentWithKind (setup.lens .firstLens) ∧
    HasFocalSignConsistentWithKind (setup.lens .secondLens) ∧
    axialPositionInCentimeters setup .object <
      axialPositionInCentimeters setup .firstLensCenter ∧
    axialPositionInCentimeters setup .firstLensCenter <
      axialPositionInCentimeters setup .secondLensCenter ∧
    axialPositionInCentimeters setup .secondLensCenter <
      axialPositionInCentimeters setup .finalImage

/-
Facts read directly from the prose and raster figure: the object and image
orientations, the real final image, the horizontal principal axis, the three
visible separations, and the second lens's known focal length. No value for the
first focal length or the intermediate-image position occurs here.
-/
def MatchesProblemAndFigureReadouts (setup : TwoLensImagingSetup) : Prop :=
  setup.objectSizeRegime = .small ∧
    setup.objectOrientation = .upright ∧
    setup.finalImageNature = .real ∧
    setup.finalImageOrientation = .inverted ∧
    setup.showsPrincipalAxis = true ∧
    firstLensObjectDistanceInCentimeters setup = 25.0 ∧
    axialPositionInCentimeters setup .secondLensCenter -
        axialPositionInCentimeters setup .firstLensCenter = 30.0 ∧
    secondLensImageDistanceInCentimeters setup = 17.0 ∧
    focalLengthInCentimeters (setup.lens .secondLens) = 12.0

/-
The governing Gaussian thin-lens equations under the Cartesian sign
convention `1/f = 1/dₒ + 1/dᵢ`. The same `intermediateImage` coordinate is the
signed image of the first lens and the object for the second lens. These are
general laws and contain no problem-specific value for the requested focal
length.
-/
structure SatisfiesParaxialTwoLensLaws (setup : TwoLensImagingSetup) : Prop where
  firstLensThinLensEquation :
    1 / focalLengthInCentimeters (setup.lens .firstLens) =
      1 / firstLensObjectDistanceInCentimeters setup +
        1 / firstLensImageDistanceInCentimeters setup
  secondLensThinLensEquation :
    1 / focalLengthInCentimeters (setup.lens .secondLens) =
      1 / secondLensObjectDistanceInCentimeters setup +
        1 / secondLensImageDistanceInCentimeters setup

/-- Labels of the four displayed focal-length choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Signed focal-length readout printed beside each answer choice, in centimeters. -/
def AnswerChoice.focalLengthInCentimeters : AnswerChoice → ℝ
  | .A => -23.0
  | .B => -21.0
  | .C => -19.0
  | .D => -17.0

/-
A modeled focal length matches a value printed to one decimal place when it
differs from that value by at most `0.05 cm`.
-/
def MatchesAnswerToNearestTenth
    (setup : TwoLensImagingSetup) (choice : AnswerChoice) : Prop :=
  |focalLengthInCentimeters (setup.lens .firstLens) -
      choice.focalLengthInCentimeters| ≤ (1 : ℝ) / 20

/-
The converging lens's equation determines its object distance to be
`204/5 cm = 40.8 cm`.
-/
lemma secondLensObjectDistance_eq_two_hundred_four_fifths
    (setup : TwoLensImagingSetup)
    (h_figure : MatchesProblemAndFigureReadouts setup)
    (h_laws : SatisfiesParaxialTwoLensLaws setup) :
    secondLensObjectDistanceInCentimeters setup = 204 / 5 := by
  rcases h_figure with ⟨_, _, _, _, _, _, _, h_di₂, h_f₂⟩
  have h_eq := h_laws.secondLensThinLensEquation
  rw [h_f₂, h_di₂] at h_eq
  have h_ne : secondLensObjectDistanceInCentimeters setup ≠ 0 := by
    intro h_zero
    rw [h_zero] at h_eq
    norm_num at h_eq
  field_simp [h_ne] at h_eq
  norm_num at h_eq ⊢
  linarith

/-
Because the lens centers are `30 cm` apart, the first lens's intermediate
image is `54/5 cm = 10.8 cm` to its left, hence has signed image distance
`-54/5 cm`.
-/
lemma firstLensImageDistance_eq_negative_fifty_four_fifths
    (setup : TwoLensImagingSetup)
    (h_figure : MatchesProblemAndFigureReadouts setup)
    (h_laws : SatisfiesParaxialTwoLensLaws setup) :
    firstLensImageDistanceInCentimeters setup = -(54 / 5) := by
  have h_object :=
    secondLensObjectDistance_eq_two_hundred_four_fifths setup h_figure h_laws
  rcases h_figure with ⟨_, _, _, _, _, _, h_separation, _, _⟩
  unfold firstLensImageDistanceInCentimeters
  unfold secondLensObjectDistanceInCentimeters at h_object
  linarith

/-
Applying the first thin-lens equation to object distance `25 cm` and signed
image distance `-54/5 cm` gives focal length `-1350/71 cm`, approximately
`-19.0 cm`. It therefore matches displayed choice C to the nearest tenth.

This formalizes `thm:physics:phyx_mini_0148:target`.
-/
theorem problem_phyx_mini_0148
    (setup : TwoLensImagingSetup)
    (h_physical : HasPhysicalTwoLensConfiguration setup)
    (h_figure : MatchesProblemAndFigureReadouts setup)
    (h_laws : SatisfiesParaxialTwoLensLaws setup) :
    focalLengthInCentimeters (setup.lens .firstLens) = -(1350 / 71) ∧
      MatchesAnswerToNearestTenth setup .C := by
  have h_image :=
    firstLensImageDistance_eq_negative_fifty_four_fifths setup h_figure h_laws
  rcases h_figure with ⟨_, _, _, _, _, h_object, _, _, _⟩
  have h_eq := h_laws.firstLensThinLensEquation
  rw [h_object, h_image] at h_eq
  have h_ne : focalLengthInCentimeters (setup.lens .firstLens) ≠ 0 := by
    intro h_zero
    rw [h_zero] at h_eq
    norm_num at h_eq
  field_simp [h_ne] at h_eq
  have h_focal :
      focalLengthInCentimeters (setup.lens .firstLens) = -(1350 / 71) := by
    norm_num at h_eq ⊢
    linarith
  constructor
  · exact h_focal
  · unfold MatchesAnswerToNearestTenth AnswerChoice.focalLengthInCentimeters
    rw [h_focal]
    norm_num [abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0148
