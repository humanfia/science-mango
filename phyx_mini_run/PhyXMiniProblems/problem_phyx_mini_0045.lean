import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0045

open Dimension

/-!
# Eyeglass focal length for a myopic eye

The far point and the lens-to-eye vertex distance are physical lengths.  The
image and focal distances are signed: a virtual image on the incident-light
side of the eyeglass lens has a negative readout.  Scalar real numbers occur
only as centimeter readouts of these dimensionful quantities.

The primary figure shows an object at infinity, rays parallel to the optical
axis before the lens, a diverging lens, and backward extensions of the
emergent rays meeting at a virtual image.  Its printed numerical value
`s' = f = -48 cm` is the conclusion to be derived, not a figure hypothesis.
-/

/-- A signed physical length, independent of the unit chosen to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices whose length component is the centimeter used in the source. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar centimeter readout of a dimensionful length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The two thin-lens types distinguished by the sign of focal length. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- A paraxial eyeglass lens represented by its signed physical focal length. -/
structure EyeglassLens where
  kind : ThinLensKind
  focalLength : LengthQuantity

/-- The distance-labeled optical states needed for this problem. -/
inductive ObjectLocation where
  | atFiniteDistance (distanceFromLens : LengthQuantity)
  | atInfinity

/-- The relation of an incident ray bundle to the figure's optical axis. -/
inductive IncidentRayGeometry where
  | general
  | parallelToOpticalAxis
  deriving DecidableEq, Repr

/-- A myopic eye together with its finite unaided far-point distance. -/
structure MyopicEye where
  farPointDistanceInFrontOfEye : LengthQuantity

/--
The physical objects and labeled distances in the eyeglass correction setup.

`signedVirtualImageDistanceFromLens` is negative when the image is virtual and
lies in front of the lens, on the same side as the object.  The lens is a
positive distance in front of the eye.
-/
structure EyeglassCorrectionSetup where
  eye : MyopicEye
  lens : EyeglassLens
  lensDistanceInFrontOfEye : LengthQuantity
  objectLocation : ObjectLocation
  incidentRayGeometry : IncidentRayGeometry
  signedVirtualImageDistanceFromLens : LengthQuantity

/-- The two numerical distances explicitly supplied by the problem. -/
def HasStatedDistanceReadouts (setup : EyeglassCorrectionSetup) : Prop :=
  lengthInCentimeters setup.eye.farPointDistanceInFrontOfEye = 50 ∧
    lengthInCentimeters setup.lensDistanceInFrontOfEye = 2

/--
Qualitative readouts from the primary figure: the lens is diverging, the
object is at infinity, and the incident rays are parallel to the optical axis.
-/
def MatchesPrimaryFigure (setup : EyeglassCorrectionSetup) : Prop :=
  setup.lens.kind = .diverging ∧
    setup.objectLocation = .atInfinity ∧
    setup.incidentRayGeometry = .parallelToOpticalAxis

/--
The axial placement described in the text: both stated distances are positive
and the spectacle lens lies between the far point and the eye.
-/
def HasPhysicalAxialPlacement (setup : EyeglassCorrectionSetup) : Prop :=
  0 < lengthInCentimeters setup.lensDistanceInFrontOfEye ∧
    lengthInCentimeters setup.lensDistanceInFrontOfEye <
      lengthInCentimeters setup.eye.farPointDistanceInFrontOfEye

/--
The correction requirement: to be clear to the unaided myopic eye, the lens's
virtual image must lie at the eye's far point.  With distances from the eye
given as positive magnitudes, its signed lens-relative distance is
`-(farPointDistance - lensToEyeDistance)`.  The relation is required in every
choice of units, so it is not tied to the centimeter readout.
-/
def FormsVirtualImageAtFarPoint (setup : EyeglassCorrectionSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.signedVirtualImageDistanceFromLens units =
      -(setup.eye.farPointDistanceInFrontOfEye units -
        setup.lensDistanceInFrontOfEye units)

/--
The paraxial thin-lens law in the infinite-object branch shown by the figure:
when incident rays are parallel to the optical axis, their signed image
distance equals the signed focal length.  This governing law contains no
numerical answer.
-/
def ObeysParallelRayFocalLaw (setup : EyeglassCorrectionSetup) : Prop :=
  setup.objectLocation = .atInfinity →
    setup.incidentRayGeometry = .parallelToOpticalAxis →
      ∀ units : UnitChoices,
        setup.lens.focalLength units =
          setup.signedVirtualImageDistanceFromLens units

/-- The four answer-choice labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The signed focal-length readout printed beside each choice, in centimeters. -/
def answerFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => -35
  | .B => -48
  | .C => -37
  | .D => -43

/--
The supplied distances and clear-vision requirement place the virtual image
`48 cm` in front of the eyeglass lens, hence at signed distance `-48 cm`.
-/
lemma virtual_image_distance_eq_neg_48
    (setup : EyeglassCorrectionSetup)
    (h_readouts : HasStatedDistanceReadouts setup)
    (h_clear : FormsVirtualImageAtFarPoint setup) :
    lengthInCentimeters setup.signedVirtualImageDistanceFromLens = -48 := by
  rcases h_readouts with ⟨h_far, h_lens⟩
  have h_clear_cm :=
    congrArg WithDim.val (h_clear centimeterUnitChoices)
  change
    lengthInCentimeters setup.signedVirtualImageDistanceFromLens =
      -(lengthInCentimeters setup.eye.farPointDistanceInFrontOfEye -
        lengthInCentimeters setup.lensDistanceInFrontOfEye)
    at h_clear_cm
  rw [h_clear_cm, h_far, h_lens]
  norm_num

/--
An object at infinity produces parallel incident rays, so the image distance
equals the focal distance.  The required diverging eyeglass lens therefore has
focal length `-48 cm`, which is answer choice B.

This formalizes `thm:physics:phyx_mini_0045:target`.
-/
theorem problem_phyx_mini_0045
    (setup : EyeglassCorrectionSetup)
    (h_readouts : HasStatedDistanceReadouts setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_placement : HasPhysicalAxialPlacement setup)
    (h_clear : FormsVirtualImageAtFarPoint setup)
    (h_parallel_law : ObeysParallelRayFocalLaw setup) :
    lengthInCentimeters setup.lens.focalLength = -48 ∧
      lengthInCentimeters setup.lens.focalLength =
        answerFocalLengthInCentimeters .B := by
  have h_image :=
    virtual_image_distance_eq_neg_48 setup h_readouts h_clear
  rcases h_figure with ⟨_, h_infinite, h_parallel⟩
  have h_focal_cm :=
    congrArg WithDim.val
      (h_parallel_law h_infinite h_parallel centimeterUnitChoices)
  change
    lengthInCentimeters setup.lens.focalLength =
      lengthInCentimeters setup.signedVirtualImageDistanceFromLens
    at h_focal_cm
  have h_focal := h_focal_cm.trans h_image
  constructor
  · exact h_focal
  · simpa [answerFocalLengthInCentimeters] using h_focal

end PhyXMiniProblems.ProblemPhyXMini0045
