import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0077

open Dimension

/-!
# Final image height in a lens--mirror round trip

The object is `5.0 cm` to the left of a converging thin lens.  A convex mirror
is `5.0 cm` to the right of the lens, so the light crosses the same lens before
and after reflection.  The primary figure gives an upright object height of
`1.0 cm` and the signed paraxial focal readouts `f₁ = 10 cm` and
`f₂ = -30 cm`.

Lengths are represented by Physlib dimensionful quantities.  Real numbers are
used only for calibrated centimeter readouts, dimensionless paraxial slopes,
and signed transverse coordinates.  The reflected path is unfolded into a
local coordinate increasing in the direction in which the returning light
travels.
-/

/-- A nonnegative physical length magnitude, independent of the chosen units. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The scalar readout of a physical length magnitude in centimeters. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Labels for the three physical elements explicitly visible in the figure. -/
inductive FigureLabel where
  | objectArrow
  | lensF1
  | mirrorF2
  deriving DecidableEq, Repr

/-- The optical classification of a thin lens. -/
inductive LensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- The optical classification of a spherical mirror. -/
inductive MirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Orientation relative to the upright source arrow. -/
inductive ArrowOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- The approximation used to model the optical system. -/
inductive OpticalApproximation where
  | exactRayTracing
  | thinParaxial
  deriving DecidableEq, Repr

/-- The source arrow and its physical height. -/
structure ObjectArrow where
  label : FigureLabel
  height : LengthMagnitude
  orientation : ArrowOrientation

/-- The thin lens carrying the printed focal label `f₁`. -/
structure ThinLens where
  label : FigureLabel
  kind : LensKind
  focalLengthMagnitude : LengthMagnitude

/-- The spherical mirror carrying the printed focal label `f₂`. -/
structure SphericalMirror where
  label : FigureLabel
  kind : MirrorKind
  focalLengthMagnitude : LengthMagnitude

/-!
The final image is not shown in the setup figure.  Its height, orientation,
and location on the returning-light side are unknown parts of the model, not
definitions made from the recorded answer.
-/
structure FinalImage where
  height : LengthMagnitude
  orientation : ArrowOrientation
  distanceFromLensOnReturnSide : LengthMagnitude

/-- The dimensionful data and labeled components of the pictured round trip. -/
structure LensMirrorRoundTrip where
  sourceObject : ObjectArrow
  lens : ThinLens
  mirror : SphericalMirror
  objectLensSeparation : LengthMagnitude
  lensMirrorSeparation : LengthMagnitude
  finalImage : FinalImage
  approximation : OpticalApproximation

/-- Signed transverse height: upright is positive and inverted is negative. -/
def signedArrowHeightInCentimeters
    (orientation : ArrowOrientation) (height : LengthMagnitude) : ℝ :=
  match orientation with
  | .upright => lengthInCentimeters height
  | .inverted => -lengthInCentimeters height

/-!
The lens sign is its outgoing focal displacement on the initial left-to-right
pass.  Thus the converging lens in the figure has positive signed focal length.
-/
def signedLensFocalLengthInCentimeters (lens : ThinLens) : ℝ :=
  match lens.kind with
  | .converging => lengthInCentimeters lens.focalLengthMagnitude
  | .diverging => -lengthInCentimeters lens.focalLengthMagnitude

/-!
The mirror sign is the focal parameter in the unfolded paraxial ray-transfer
law.  It is positive for a focusing concave mirror and negative for a
diverging convex mirror.  The primary figure shows the latter and prints
`f₂ = -30 cm`.
-/
def signedMirrorFocalLengthInCentimeters (mirror : SphericalMirror) : ℝ :=
  match mirror.kind with
  | .concave => lengthInCentimeters mirror.focalLengthMagnitude
  | .convex => -lengthInCentimeters mirror.focalLengthMagnitude

/-- A scalar paraxial-ray state in a local propagation coordinate. -/
structure ParaxialRay where
  transverseHeightInCentimeters : ℝ
  /-- The small-angle slope `dy/dx`, which is dimensionless. -/
  slope : ℝ

/-- Free paraxial propagation through the given axial distance. -/
def propagateParaxialRay
    (axialDistanceInCentimeters : ℝ) (ray : ParaxialRay) : ParaxialRay where
  transverseHeightInCentimeters :=
    ray.transverseHeightInCentimeters + axialDistanceInCentimeters * ray.slope
  slope := ray.slope

/-!
Ideal thin-lens refraction in the local propagation coordinate.  This is the
ray form of the Gaussian thin-lens law and contains no problem-specific answer.
-/
def traverseThinLens (lens : ThinLens) (ray : ParaxialRay) : ParaxialRay where
  transverseHeightInCentimeters := ray.transverseHeightInCentimeters
  slope := ray.slope -
    ray.transverseHeightInCentimeters /
      signedLensFocalLengthInCentimeters lens

/-!
Ideal spherical-mirror reflection after unfolding the reflected half-space.
The mirror focal readout already incorporates the factor of two between the
curvature radius and the focal length.
-/
def reflectFromSphericalMirrorUnfolded
    (mirror : SphericalMirror) (ray : ParaxialRay) : ParaxialRay where
  transverseHeightInCentimeters := ray.transverseHeightInCentimeters
  slope := ray.slope -
    ray.transverseHeightInCentimeters /
      signedMirrorFocalLengthInCentimeters mirror

/-- A ray leaving the top of the source arrow with arbitrary initial slope. -/
def sourceRay (setup : LensMirrorRoundTrip) (initialSlope : ℝ) : ParaxialRay where
  transverseHeightInCentimeters :=
    signedArrowHeightInCentimeters setup.sourceObject.orientation
      setup.sourceObject.height
  slope := initialSlope

/-!
The full sequence is object-to-lens propagation, the first lens traversal,
lens-to-mirror propagation, reflection, the unfolded return propagation,
the second traversal of the same lens, and propagation to the final plane.
-/
def rayAtFinalImagePlane
    (setup : LensMirrorRoundTrip) (initialSlope : ℝ) : ParaxialRay :=
  let rayAtFirstLens := propagateParaxialRay
    (lengthInCentimeters setup.objectLensSeparation) (sourceRay setup initialSlope)
  let rayAfterFirstLens := traverseThinLens setup.lens rayAtFirstLens
  let rayAtMirror := propagateParaxialRay
    (lengthInCentimeters setup.lensMirrorSeparation) rayAfterFirstLens
  let rayAfterMirror := reflectFromSphericalMirrorUnfolded setup.mirror rayAtMirror
  let rayAtSecondLens := propagateParaxialRay
    (lengthInCentimeters setup.lensMirrorSeparation) rayAfterMirror
  let rayAfterSecondLens := traverseThinLens setup.lens rayAtSecondLens
  propagateParaxialRay
    (lengthInCentimeters setup.finalImage.distanceFromLensOnReturnSide)
    rayAfterSecondLens

/-!
Labels, optical kinds, approximation, and numerical readouts taken from the
primary figure.  This predicate gives no final-image height, distance, or
orientation.
-/
def MatchesFigureReadouts (setup : LensMirrorRoundTrip) : Prop :=
  setup.sourceObject.label = .objectArrow ∧
    setup.lens.label = .lensF1 ∧
    setup.mirror.label = .mirrorF2 ∧
    setup.sourceObject.orientation = .upright ∧
    setup.lens.kind = .converging ∧
    setup.mirror.kind = .convex ∧
    setup.approximation = .thinParaxial ∧
    lengthInCentimeters setup.sourceObject.height = 1.0 ∧
    lengthInCentimeters setup.objectLensSeparation = 5.0 ∧
    lengthInCentimeters setup.lensMirrorSeparation = 5.0 ∧
    signedLensFocalLengthInCentimeters setup.lens = 10 ∧
    signedMirrorFocalLengthInCentimeters setup.mirror = -30

/-!
Strict positivity selects the nondegenerate physical branch.  It does not
assign any numerical value to the unknown final-image quantities.
-/
def HasPhysicalLengthMagnitudes (setup : LensMirrorRoundTrip) : Prop :=
  0 < lengthInCentimeters setup.sourceObject.height ∧
    0 < lengthInCentimeters setup.lens.focalLengthMagnitude ∧
    0 < lengthInCentimeters setup.mirror.focalLengthMagnitude ∧
    0 < lengthInCentimeters setup.objectLensSeparation ∧
    0 < lengthInCentimeters setup.lensMirrorSeparation ∧
    0 < lengthInCentimeters setup.finalImage.height ∧
    0 < lengthInCentimeters setup.finalImage.distanceFromLensOnReturnSide

/-!
Paraxial image formation means that every ray emitted from the top of the
source reaches a common signed transverse point in the final plane.  This is a
general convergence law; it does not specify the requested numerical height.
-/
def SatisfiesParaxialRoundTripImagingLaw (setup : LensMirrorRoundTrip) : Prop :=
  ∀ initialSlope : ℝ,
    (rayAtFinalImagePlane setup initialSlope).transverseHeightInCentimeters =
      signedArrowHeightInCentimeters setup.finalImage.orientation
        setup.finalImage.height

/-!
The zero-slope and unit-slope source rays determine the common image plane to
be `30 cm` from the lens on the returning-light side.
-/
lemma finalImageDistanceInCentimeters_eq_thirty
    (setup : LensMirrorRoundTrip)
    (h_physical : HasPhysicalLengthMagnitudes setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_imaging : SatisfiesParaxialRoundTripImagingLaw setup) :
    lengthInCentimeters setup.finalImage.distanceFromLensOnReturnSide = 30 := by
  have h_zero := h_imaging 0
  have h_one := h_imaging 1
  rcases h_figure with
    ⟨_, _, _, h_source_orientation, _, _, _, h_source_height,
      h_object_distance, h_mirror_distance, h_lens, h_mirror⟩
  norm_num [rayAtFinalImagePlane, sourceRay, propagateParaxialRay,
    traverseThinLens, reflectFromSphericalMirrorUnfolded,
    h_source_orientation, signedArrowHeightInCentimeters, h_source_height,
    h_object_distance, h_mirror_distance, h_lens, h_mirror] at h_zero h_one
  linarith

/-!
At the common plane the signed transverse height is `-8/3 cm`; the negative
sign records inversion, while the physical height magnitude is `8/3 cm`.
-/
lemma signedFinalImageHeightInCentimeters_eq
    (setup : LensMirrorRoundTrip)
    (h_physical : HasPhysicalLengthMagnitudes setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_imaging : SatisfiesParaxialRoundTripImagingLaw setup) :
    signedArrowHeightInCentimeters setup.finalImage.orientation
      setup.finalImage.height = -(8 / 3 : ℝ) := by
  have h_distance := finalImageDistanceInCentimeters_eq_thirty
    setup h_physical h_figure h_imaging
  rcases h_figure with
    ⟨_, _, _, h_source_orientation, _, _, _, h_source_height,
      h_object_distance, h_mirror_distance, h_lens, h_mirror⟩
  have h_zero := h_imaging 0
  norm_num [rayAtFinalImagePlane, sourceRay, propagateParaxialRay,
    traverseThinLens, reflectFromSphericalMirrorUnfolded,
    h_source_orientation, signedArrowHeightInCentimeters, h_source_height,
    h_object_distance, h_mirror_distance, h_lens, h_mirror, h_distance] at h_zero ⊢
  linarith

/-- Labels of the four displayed image-height answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The final-image height in centimeters printed beside each answer label. -/
def displayedImageHeightInCentimeters : AnswerChoice → ℝ
  | .A => 1.4
  | .B => 2.6
  | .C => 2.7
  | .D => 1.95

/-- Half a unit in the final printed decimal place of an answer choice. -/
def displayedHeightTolerance : AnswerChoice → ℝ
  | .A => 0.05
  | .B => 0.05
  | .C => 0.05
  | .D => 0.005

/-- A physical height agrees with the displayed rounded answer. -/
def MatchesDisplayedImageHeight
    (height : LengthMagnitude) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters height - displayedImageHeightInCentimeters choice| ≤
    displayedHeightTolerance choice

/-!
The pictured round trip produces an inverted final image of exact physical
height `8/3 cm`, which rounds to `2.7 cm`, answer choice C.

This formalizes `thm:physics:phyx_mini_0077:target`.
-/
theorem problem_phyx_mini_0077
    (setup : LensMirrorRoundTrip)
    (h_physical : HasPhysicalLengthMagnitudes setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_imaging : SatisfiesParaxialRoundTripImagingLaw setup) :
    lengthInCentimeters setup.finalImage.height = (8 / 3 : ℝ) ∧
      setup.finalImage.orientation = .inverted ∧
      MatchesDisplayedImageHeight setup.finalImage.height .C := by
  have h_signed := signedFinalImageHeightInCentimeters_eq
    setup h_physical h_figure h_imaging
  have h_height_pos := h_physical.2.2.2.2.2.1
  cases h_orientation : setup.finalImage.orientation with
  | upright =>
      simp [signedArrowHeightInCentimeters, h_orientation] at h_signed
      linarith
  | inverted =>
      simp [signedArrowHeightInCentimeters, h_orientation] at h_signed
      have h_height :
          lengthInCentimeters setup.finalImage.height = (8 / 3 : ℝ) := by
        linarith
      refine ⟨h_height, rfl, ?_⟩
      norm_num [MatchesDisplayedImageHeight, displayedImageHeightInCentimeters,
        displayedHeightTolerance, h_height, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0077
