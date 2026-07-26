import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0034

/-!
# Focal length of a concave mirror followed by a converging lens

The figure places, from left to right, a concave mirror, an upright object, a
converging lens, two coincident real images, and the observer's eye.  There are
two optical paths to the image plane: a direct passage through the lens and a
passage that first reflects from the mirror and then traverses the lens.

Axial locations and focal lengths are dimensionful signed lengths.  Scalar
equations below use centimeter readouts throughout.  Signed transverse
magnification records orientation: positive is upright and negative inverted.
-/

/-- A signed physical length whose value transforms coherently with unit choice. -/
abbrev OpticalLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The physical length with scalar readout `magnitude` in the selected unit. -/
def lengthIn (unit : LengthUnit) (magnitude : ℝ) : OpticalLength :=
  CarriesDimension.toDimensionful { UnitChoices.SI with length := unit } ⟨magnitude⟩

/-- The signed scalar readout of a physical length in centimeters. -/
def centimetersValue (length : OpticalLength) : ℝ :=
  (length { UnitChoices.SI with length := LengthUnit.centimeters }).val

/-- Directed axial separation, in centimeters, from `start` to `finish`. -/
def axialSeparationCm (start finish : OpticalLength) : ℝ :=
  centimetersValue finish - centimetersValue start

/-- The paraxial lens types, distinguished by the sign of focal length. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- The spherical-mirror types as viewed from the incident-light side. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Orientation of an image relative to the upright object. -/
inductive ImageOrientation where
  | upright
  | inverted
  deriving DecidableEq, Repr

/-- Whether geometrical-optics rays actually meet at an image or only appear to. -/
inductive ImageReality where
  | real
  | virtual
  deriving DecidableEq, Repr

/--
The physical elements, labeled image locations, and path magnifications in the
mirror--lens diagram.

`mirrorIntermediateImageAxialPosition` is the image that the mirror alone
would form.  It is the effective object location for the reflected path's
subsequent traversal of the lens; it is not assumed to coincide with the
original object.
-/
structure MirrorLensSetup where
  /-- Figure label `Mirror`. -/
  mirrorAxialPosition : OpticalLength
  /-- Figure label `Object`. -/
  objectAxialPosition : OpticalLength
  /-- Figure label `Lens`. -/
  lensAxialPosition : OpticalLength
  /-- Image location produced by the direct object-to-lens path. -/
  directImageAxialPosition : OpticalLength
  /-- Image location produced by the mirror-then-lens path. -/
  reflectedImageAxialPosition : OpticalLength
  /-- Effective intermediate image formed by the mirror alone. -/
  mirrorIntermediateImageAxialPosition : OpticalLength
  /-- Position of the observer's eye, shown to the right of the images. -/
  observerAxialPosition : OpticalLength
  lensKind : ThinLensKind
  mirrorKind : SphericalMirrorKind
  lensFocalLength : OpticalLength
  mirrorFocalLength : OpticalLength
  directImageOrientation : ImageOrientation
  reflectedImageOrientation : ImageOrientation
  directImageReality : ImageReality
  reflectedImageReality : ImageReality
  /-- Signed magnification for the direct pass through the lens. -/
  directPathMagnification : ℝ
  /-- Signed magnification produced by the mirror encounter alone. -/
  mirrorStageMagnification : ℝ
  /-- Signed magnification on the reflected path's subsequent lens encounter. -/
  reflectedLensStageMagnification : ℝ
  /-- Net signed magnification for the mirror-then-lens path. -/
  reflectedPathMagnification : ℝ

/-- Object distance for the direct lens path, as a positive centimeter readout. -/
def directLensObjectDistanceCm (setup : MirrorLensSetup) : ℝ :=
  axialSeparationCm setup.objectAxialPosition setup.lensAxialPosition

/-- Image distance for the direct lens path, in centimeters. -/
def directLensImageDistanceCm (setup : MirrorLensSetup) : ℝ :=
  axialSeparationCm setup.lensAxialPosition setup.directImageAxialPosition

/-- Object distance at the mirror, measured from mirror to object in centimeters. -/
def mirrorObjectDistanceCm (setup : MirrorLensSetup) : ℝ :=
  axialSeparationCm setup.mirrorAxialPosition setup.objectAxialPosition

/-- Image distance at the mirror, measured into the reflected-light side. -/
def mirrorImageDistanceCm (setup : MirrorLensSetup) : ℝ :=
  axialSeparationCm setup.mirrorAxialPosition
    setup.mirrorIntermediateImageAxialPosition

/--
Object distance for the lens encounter after reflection.  The mirror's
intermediate image is the effective object for light incident on the lens from
the left.
-/
def reflectedLensObjectDistanceCm (setup : MirrorLensSetup) : ℝ :=
  axialSeparationCm setup.mirrorIntermediateImageAxialPosition
    setup.lensAxialPosition

/-- Image distance for the lens encounter after reflection, in centimeters. -/
def reflectedLensImageDistanceCm (setup : MirrorLensSetup) : ℝ :=
  axialSeparationCm setup.lensAxialPosition setup.reflectedImageAxialPosition

/--
Figure and numerical readouts: a concave mirror lies left of the upright
object, which lies left of a converging lens; both displayed images lie between
the lens and the eye.  The lens focal length is `+10.0 cm` and the mirror--lens
separation is `40.0 cm`.
-/
def MatchesFigureAndGivenLengths (setup : MirrorLensSetup) : Prop :=
  setup.lensKind = .converging ∧
    setup.mirrorKind = .concave ∧
    centimetersValue setup.mirrorAxialPosition <
      centimetersValue setup.objectAxialPosition ∧
    centimetersValue setup.objectAxialPosition <
      centimetersValue setup.lensAxialPosition ∧
    centimetersValue setup.lensAxialPosition <
      centimetersValue setup.directImageAxialPosition ∧
    centimetersValue setup.lensAxialPosition <
      centimetersValue setup.reflectedImageAxialPosition ∧
    centimetersValue setup.directImageAxialPosition <
      centimetersValue setup.observerAxialPosition ∧
    centimetersValue setup.reflectedImageAxialPosition <
      centimetersValue setup.observerAxialPosition ∧
    centimetersValue setup.lensFocalLength = 10 ∧
    axialSeparationCm setup.mirrorAxialPosition setup.lensAxialPosition = 40

/--
Observed image data: the two real images occupy the same location, the direct
image is inverted, the reflected-path image is upright, and their signed
magnifications are respectively `-1.50` and `+1.50`.
-/
def HasObservedCoincidentImages (setup : MirrorLensSetup) : Prop :=
  setup.directImageAxialPosition = setup.reflectedImageAxialPosition ∧
    setup.directImageReality = .real ∧
    setup.reflectedImageReality = .real ∧
    setup.directImageOrientation = .inverted ∧
    setup.reflectedImageOrientation = .upright ∧
    setup.directPathMagnification = -(3 / 2) ∧
    setup.reflectedPathMagnification = 3 / 2

/--
The paraxial Gaussian imaging law `1/f = 1/p + 1/q`, in the division-free,
dimensionally homogeneous form `f * (p + q) = p * q`.  All three arguments
are centimeter readouts of signed lengths.
-/
def GaussianImagingLawCm (focalLength : OpticalLength)
    (objectDistanceCm imageDistanceCm : ℝ) : Prop :=
  centimetersValue focalLength * (objectDistanceCm + imageDistanceCm) =
    objectDistanceCm * imageDistanceCm

/-- The signed transverse-magnification law `m = -q/p`, without division. -/
def TransverseMagnificationLawCm
    (objectDistanceCm imageDistanceCm magnification : ℝ) : Prop :=
  magnification * objectDistanceCm = -imageDistanceCm

/-- The net magnification of the mirror and subsequent lens is their product. -/
def TwoStageMagnificationLaw (setup : MirrorLensSetup) : Prop :=
  setup.reflectedPathMagnification =
    setup.mirrorStageMagnification * setup.reflectedLensStageMagnification

/-- The direct path fixes the lens object and image distances. -/
lemma directPathDistances_eq
    (setup : MirrorLensSetup)
    (h_figure : MatchesFigureAndGivenLengths setup)
    (h_observed : HasObservedCoincidentImages setup)
    (h_direct_imaging :
      GaussianImagingLawCm setup.lensFocalLength
        (directLensObjectDistanceCm setup) (directLensImageDistanceCm setup))
    (h_direct_magnification :
      TransverseMagnificationLawCm
        (directLensObjectDistanceCm setup) (directLensImageDistanceCm setup)
        setup.directPathMagnification) :
    directLensObjectDistanceCm setup = 50 / 3 ∧
      directLensImageDistanceCm setup = 25 := by
  rcases h_figure with
    ⟨_, _, _, h_object_lens, _, _, _, _, h_lens_focal, _⟩
  rcases h_observed with ⟨_, _, _, _, _, h_direct_mag, _⟩
  have h_object_distance_pos : 0 < directLensObjectDistanceCm setup := by
    unfold directLensObjectDistanceCm axialSeparationCm
    linarith
  simp only [GaussianImagingLawCm, h_lens_focal] at h_direct_imaging
  simp only [TransverseMagnificationLawCm, h_direct_mag] at h_direct_magnification
  constructor <;>
    norm_num at h_direct_imaging h_direct_magnification ⊢ <;>
    nlinarith

/--
Because the same lens sends both paths to the same final image plane, the
mirror's intermediate image must coincide axially with the original object.
-/
lemma mirrorIntermediateImage_coincides_with_object
    (setup : MirrorLensSetup)
    (h_figure : MatchesFigureAndGivenLengths setup)
    (h_observed : HasObservedCoincidentImages setup)
    (h_direct_imaging :
      GaussianImagingLawCm setup.lensFocalLength
        (directLensObjectDistanceCm setup) (directLensImageDistanceCm setup))
    (h_direct_magnification :
      TransverseMagnificationLawCm
        (directLensObjectDistanceCm setup) (directLensImageDistanceCm setup)
        setup.directPathMagnification)
    (h_reflected_lens_imaging :
      GaussianImagingLawCm setup.lensFocalLength
        (reflectedLensObjectDistanceCm setup)
        (reflectedLensImageDistanceCm setup)) :
    setup.mirrorIntermediateImageAxialPosition = setup.objectAxialPosition := by
  have h_direct := directPathDistances_eq setup h_figure h_observed
    h_direct_imaging h_direct_magnification
  rcases h_figure with ⟨_, _, _, _, _, _, _, _, h_lens_focal, _⟩
  rcases h_observed with ⟨h_coincident, _, _, _, _, _, _⟩
  have h_reflected_image_distance :
      reflectedLensImageDistanceCm setup = 25 := by
    simpa [reflectedLensImageDistanceCm, directLensImageDistanceCm,
      h_coincident] using h_direct.2
  unfold GaussianImagingLawCm at h_reflected_lens_imaging
  rw [h_lens_focal, h_reflected_image_distance] at h_reflected_lens_imaging
  have h_reflected_object_distance :
      reflectedLensObjectDistanceCm setup = 50 / 3 := by
    norm_num at h_reflected_lens_imaging ⊢
    linarith
  have h_equal_object_distances :=
    h_reflected_object_distance.trans h_direct.1.symm
  have h_readout :
      centimetersValue setup.mirrorIntermediateImageAxialPosition =
        centimetersValue setup.objectAxialPosition := by
    unfold reflectedLensObjectDistanceCm directLensObjectDistanceCm
      axialSeparationCm at h_equal_object_distances
    linarith
  apply Dimensionful.ext
  funext units
  rw [setup.mirrorIntermediateImageAxialPosition.property
        { UnitChoices.SI with length := LengthUnit.centimeters } units,
      setup.objectAxialPosition.property
        { UnitChoices.SI with length := LengthUnit.centimeters } units]
  congr 1
  exact WithDim.ext _ _ h_readout

/--
The supplied geometry and imaging laws determine the mirror focal length
exactly as `35/3 cm`.
-/
lemma mirrorFocalLength_eq
    (setup : MirrorLensSetup)
    (h_figure : MatchesFigureAndGivenLengths setup)
    (h_observed : HasObservedCoincidentImages setup)
    (h_direct_imaging :
      GaussianImagingLawCm setup.lensFocalLength
        (directLensObjectDistanceCm setup) (directLensImageDistanceCm setup))
    (h_direct_magnification :
      TransverseMagnificationLawCm
        (directLensObjectDistanceCm setup) (directLensImageDistanceCm setup)
        setup.directPathMagnification)
    (h_mirror_imaging :
      GaussianImagingLawCm setup.mirrorFocalLength
        (mirrorObjectDistanceCm setup) (mirrorImageDistanceCm setup))
    (h_reflected_lens_imaging :
      GaussianImagingLawCm setup.lensFocalLength
        (reflectedLensObjectDistanceCm setup)
        (reflectedLensImageDistanceCm setup)) :
    centimetersValue setup.mirrorFocalLength = 35 / 3 := by
  have h_direct := directPathDistances_eq setup h_figure h_observed
    h_direct_imaging h_direct_magnification
  have h_intermediate := mirrorIntermediateImage_coincides_with_object setup
    h_figure h_observed h_direct_imaging h_direct_magnification
    h_reflected_lens_imaging
  rcases h_figure with
    ⟨_, _, _, _, _, _, _, _, _, h_mirror_lens_distance⟩
  have h_mirror_object_distance : mirrorObjectDistanceCm setup = 70 / 3 := by
    unfold directLensObjectDistanceCm axialSeparationCm at h_direct
    unfold axialSeparationCm at h_mirror_lens_distance
    unfold mirrorObjectDistanceCm axialSeparationCm
    norm_num at h_direct ⊢
    linarith
  have h_mirror_image_distance : mirrorImageDistanceCm setup = 70 / 3 := by
    simpa [mirrorImageDistanceCm, mirrorObjectDistanceCm, h_intermediate] using
      h_mirror_object_distance
  unfold GaussianImagingLawCm at h_mirror_imaging
  rw [h_mirror_object_distance, h_mirror_image_distance] at h_mirror_imaging
  norm_num at h_mirror_imaging ⊢
  linarith

/-- Labels of the four printed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Mirror focal-length readout printed beside each answer, in centimeters. -/
def answerFocalLengthCm : AnswerChoice → ℝ
  | .A => 111 / 10
  | .B => 105 / 10
  | .C => 87 / 10
  | .D => 117 / 10

/-- Agreement with a displayed focal length to the nearest tenth centimeter. -/
def MatchesAnswerToNearestTenth
    (focalLength : OpticalLength) (choice : AnswerChoice) : Prop :=
  |centimetersValue focalLength - answerFocalLengthCm choice| ≤ 1 / 20

/--
The concave mirror has exact focal length `+35/3 cm`, which is displayed as
`+11.7 cm`; hence the requested answer is choice D.

This formalizes `thm:physics:phyx_mini_0034:target`.
-/
theorem problem_phyx_mini_0034
    (setup : MirrorLensSetup)
    (h_figure : MatchesFigureAndGivenLengths setup)
    (h_observed : HasObservedCoincidentImages setup)
    (h_direct_imaging :
      GaussianImagingLawCm setup.lensFocalLength
        (directLensObjectDistanceCm setup) (directLensImageDistanceCm setup))
    (h_direct_magnification :
      TransverseMagnificationLawCm
        (directLensObjectDistanceCm setup) (directLensImageDistanceCm setup)
        setup.directPathMagnification)
    (h_mirror_imaging :
      GaussianImagingLawCm setup.mirrorFocalLength
        (mirrorObjectDistanceCm setup) (mirrorImageDistanceCm setup))
    (h_mirror_magnification :
      TransverseMagnificationLawCm
        (mirrorObjectDistanceCm setup) (mirrorImageDistanceCm setup)
        setup.mirrorStageMagnification)
    (h_reflected_lens_imaging :
      GaussianImagingLawCm setup.lensFocalLength
        (reflectedLensObjectDistanceCm setup)
        (reflectedLensImageDistanceCm setup))
    (h_reflected_lens_magnification :
      TransverseMagnificationLawCm
        (reflectedLensObjectDistanceCm setup)
        (reflectedLensImageDistanceCm setup)
        setup.reflectedLensStageMagnification)
    (h_composition : TwoStageMagnificationLaw setup) :
    centimetersValue setup.mirrorFocalLength = 35 / 3 ∧
      MatchesAnswerToNearestTenth setup.mirrorFocalLength .D := by
  have h_focal := mirrorFocalLength_eq setup h_figure h_observed
    h_direct_imaging h_direct_magnification h_mirror_imaging
    h_reflected_lens_imaging
  refine ⟨h_focal, ?_⟩
  simp only [MatchesAnswerToNearestTenth, answerFocalLengthCm, h_focal]
  norm_num [abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0034
