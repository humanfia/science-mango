import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0129

open Dimension

/-!
# Reading-glasses power for a farsighted eye

A farsighted eye has an unaided near point `100 cm` from the eye, while the
newspaper is to be read at `25 cm`. The reading lens is modeled as lying at
the eye. It must therefore form a virtual image of the newspaper at the
unaided near point.

The supplied ray diagram places the virtual image and object on the incident
side of a double-convex lens and the eye on its outgoing side. Solid rays
travel from the object through the lens toward the eye, while dashed backward
extensions meet at the virtual image. The figure labels the object and image
distances by `dₒ` and `dᵢ`.

Lengths and optical power are genuine Physlib dimensionful quantities. Real
numbers occur only as readouts: centimeters for the stated geometry and
inverse meters (diopters) for optical power.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical optical power, with inverse-length dimension. -/
abbrev OpticalPower : Type := Dimensionful (WithDim L𝓭⁻¹ ℝ)

/-- The scalar readout of a length magnitude in centimeters. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  ((length { UnitChoices.SI with length := LengthUnit.centimeters }).val : ℝ)

/-- The SI readout of optical power, in inverse meters, hence in diopters. -/
def powerInDiopters (power : OpticalPower) : ℝ :=
  (power UnitChoices.SI).val

/-- Labels of the physical elements visible in the supplied ray diagram. -/
inductive FigureElement where
  | image
  | object
  | lens
  | eye
  deriving DecidableEq, Repr

/-- The two distance labels displayed below the optical axis. -/
inductive FigureDistanceLabel where
  | dO
  | dI
  deriving DecidableEq, Repr

/-- The side of the lens on which a pictured optical element lies. -/
inductive LensSide where
  | incident
  | outgoing
  deriving DecidableEq, Repr

/-- The optical behavior of the thin reading lens. -/
inductive LensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Whether the image is made by rays or by their backward extensions. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The refractive state of the eye described in the problem. -/
inductive EyeCondition where
  | emmetropic
  | farsighted
  | nearsighted
  deriving DecidableEq, Repr

/-- The three ray segments distinguished by the supplied picture. -/
inductive FigureRaySegment where
  | objectToLens
  | lensToEye
  | backwardExtensionToImage
  deriving DecidableEq, Repr

/-- Whether a ray segment is drawn as an actual ray or a construction line. -/
inductive RayRendering where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- The two relevant directions along the pictured optical path. -/
inductive RayDirection where
  | towardEye
  | towardVirtualImage
  deriving DecidableEq, Repr

/-- The eye, including its unaided near-point distance. -/
structure Eye where
  label : FigureElement
  condition : EyeCondition
  sideOfLens : LensSide
  nearPointDistance : LengthMagnitude

/-- The newspaper used as the near object. -/
structure Newspaper where
  label : FigureElement
  sideOfLens : LensSide
  distanceFromEye : LengthMagnitude
  distanceFromLens : LengthMagnitude

/-- The virtual image that the reading glasses present to the unaided eye. -/
structure CorrectiveImage where
  label : FigureElement
  nature : ImageNature
  sideOfLens : LensSide
  distanceFromLens : LengthMagnitude

/-- A thin reading lens with dimensionful focal length and optical power. -/
structure ThinReadingLens where
  label : FigureElement
  kind : LensKind
  focalLengthMagnitude : LengthMagnitude
  opticalPower : OpticalPower

/-
The physical system and the figure-derived ray information. None of these
fields fixes the requested numerical optical power.
-/
structure ReadingGlassesSetup where
  eye : Eye
  newspaper : Newspaper
  image : CorrectiveImage
  lens : ThinReadingLens
  lensToEyeDistance : LengthMagnitude
  rayRendering : FigureRaySegment → RayRendering
  rayDirection : FigureRaySegment → RayDirection

/-- A converging lens has positive signed focal length in this convention. -/
def signedFocalLengthInCentimeters (lens : ThinReadingLens) : ℝ :=
  match lens.kind with
  | .converging => lengthInCentimeters lens.focalLengthMagnitude
  | .diverging => -lengthInCentimeters lens.focalLengthMagnitude

/-- A real object on the incident side has positive Gaussian object distance. -/
def signedObjectDistanceInCentimeters (object : Newspaper) : ℝ :=
  match object.sideOfLens with
  | .incident => lengthInCentimeters object.distanceFromLens
  | .outgoing => -lengthInCentimeters object.distanceFromLens

/-- A virtual image on the incident side has negative Gaussian image distance. -/
def signedImageDistanceInCentimeters (image : CorrectiveImage) : ℝ :=
  match image.sideOfLens with
  | .incident => -lengthInCentimeters image.distanceFromLens
  | .outgoing => lengthInCentimeters image.distanceFromLens

/-- The signed centimeter readout associated with each figure distance label. -/
def displayedDistanceInCentimeters
    (setup : ReadingGlassesSetup) : FigureDistanceLabel → ℝ
  | .dO => signedObjectDistanceInCentimeters setup.newspaper
  | .dI => signedImageDistanceInCentimeters setup.image

/-
Problem data: the farsighted near point is `100 cm`, the desired reading
distance is `25 cm`, and the lens-to-eye separation is neglected. No focal
length or optical-power answer is included.
-/
def MatchesProblemReadouts (setup : ReadingGlassesSetup) : Prop :=
  setup.eye.condition = .farsighted ∧
    lengthInCentimeters setup.eye.nearPointDistance = 100 ∧
    lengthInCentimeters setup.newspaper.distanceFromEye = 25 ∧
    lengthInCentimeters setup.lensToEyeDistance = 0

/-
Figure readout: image, object, lens, and eye occupy the shown sides; the lens
is double-convex/converging; the virtual-image construction is dashed and the
physical ray path toward the eye is solid. This contains no requested power.
-/
def MatchesSuppliedRayDiagram (setup : ReadingGlassesSetup) : Prop :=
  setup.image.label = .image ∧
    setup.image.nature = .virtual ∧
    setup.image.sideOfLens = .incident ∧
    setup.newspaper.label = .object ∧
    setup.newspaper.sideOfLens = .incident ∧
    setup.lens.label = .lens ∧
    setup.lens.kind = .converging ∧
    setup.eye.label = .eye ∧
    setup.eye.sideOfLens = .outgoing ∧
    setup.rayRendering .objectToLens = .solid ∧
    setup.rayRendering .lensToEye = .solid ∧
    setup.rayRendering .backwardExtensionToImage = .dashed ∧
    setup.rayDirection .objectToLens = .towardEye ∧
    setup.rayDirection .lensToEye = .towardEye ∧
    setup.rayDirection .backwardExtensionToImage = .towardVirtualImage

/-- Strict positivity of the physical length magnitudes used by the model. -/
def HasPhysicalLengthMagnitudes (setup : ReadingGlassesSetup) : Prop :=
  0 < lengthInCentimeters setup.eye.nearPointDistance ∧
    0 < lengthInCentimeters setup.newspaper.distanceFromEye ∧
    0 < lengthInCentimeters setup.newspaper.distanceFromLens ∧
    0 < lengthInCentimeters setup.image.distanceFromLens ∧
    0 < lengthInCentimeters setup.lens.focalLengthMagnitude

/-
Because the glasses are very close to the eye, the object-to-lens distance is
identified with the given object-to-eye reading distance.
-/
def UsesLensCloseToEyeApproximation (setup : ReadingGlassesSetup) : Prop :=
  lengthInCentimeters setup.newspaper.distanceFromLens =
    lengthInCentimeters setup.newspaper.distanceFromEye

/-
The corrective design condition: the lens presents a virtual image at the
unaided near point. The negative Gaussian sign is supplied separately by
`signedImageDistanceInCentimeters` and the incident-side figure placement.
-/
def FormsVirtualImageAtNearPoint (setup : ReadingGlassesSetup) : Prop :=
  setup.image.nature = .virtual ∧
    lengthInCentimeters setup.image.distanceFromLens =
      lengthInCentimeters setup.eye.nearPointDistance

/-
The Gaussian thin-lens equation `1/f = 1/dₒ + 1/dᵢ`, expressed in signed
centimeter readouts. It is a governing law, not the answer for this setup.
-/
def SatisfiesThinLensEquation (setup : ReadingGlassesSetup) : Prop :=
  1 / signedFocalLengthInCentimeters setup.lens =
    1 / displayedDistanceInCentimeters setup .dO +
      1 / displayedDistanceInCentimeters setup .dI

/-
Optical power is reciprocal focal length. Since the focal-length readout is
in centimeters and one meter is one hundred centimeters, its diopter readout
is `100 / f_cm`. This general relation contains no problem-specific number.
-/
def SatisfiesOpticalPowerLaw (lens : ThinReadingLens) : Prop :=
  powerInDiopters lens.opticalPower =
    100 / signedFocalLengthInCentimeters lens

/-- Labels of the four power choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The optical power printed beside each answer label, in diopters. -/
def displayedPowerInDiopters : AnswerChoice → ℝ
  | .A => 5
  | .B => 2
  | .C => 3
  | .D => 4

/-- Exact agreement between a modeled optical power and a displayed choice. -/
def MatchesAnswerChoice (power : OpticalPower) (choice : AnswerChoice) : Prop :=
  powerInDiopters power = displayedPowerInDiopters choice

/-
The two stated distances, virtual-image requirement, and signed thin-lens law
give reciprocal focal length `3/100 cm⁻¹`.
-/
lemma reciprocalFocalLengthInCentimeters_eq_three_hundredths
    (setup : ReadingGlassesSetup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedRayDiagram setup)
    (h_eye_plane : UsesLensCloseToEyeApproximation setup)
    (h_near_point : FormsVirtualImageAtNearPoint setup)
    (h_thin_lens : SatisfiesThinLensEquation setup) :
    1 / signedFocalLengthInCentimeters setup.lens = (3 / 100 : ℝ) := by
  unfold MatchesProblemReadouts at h_readouts
  unfold MatchesSuppliedRayDiagram at h_figure
  unfold UsesLensCloseToEyeApproximation at h_eye_plane
  unfold FormsVirtualImageAtNearPoint at h_near_point
  unfold SatisfiesThinLensEquation at h_thin_lens
  rcases h_readouts with ⟨_, h_near, h_object_eye, _⟩
  rcases h_figure with ⟨_, _, h_image_side, _, h_object_side, _⟩
  rcases h_near_point with ⟨_, h_image_near⟩
  calc
    1 / signedFocalLengthInCentimeters setup.lens =
        1 / (25 : ℝ) + 1 / (-100 : ℝ) := by
          simpa [displayedDistanceInCentimeters,
            signedObjectDistanceInCentimeters,
            signedImageDistanceInCentimeters, h_object_side, h_image_side,
            h_eye_plane, h_object_eye, h_image_near, h_near] using h_thin_lens
    _ = 3 / 100 := by norm_num

/-
The required converging reading lens has optical power `+3 D`, which is
answer choice C.

This formalizes `thm:physics:phyx_mini_0129:target`. The requested power and
choice C occur only in this conclusion, never in a premise or setup field.
-/
theorem problem_phyx_mini_0129
    (setup : ReadingGlassesSetup)
    (h_physical : HasPhysicalLengthMagnitudes setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedRayDiagram setup)
    (h_eye_plane : UsesLensCloseToEyeApproximation setup)
    (h_near_point : FormsVirtualImageAtNearPoint setup)
    (h_thin_lens : SatisfiesThinLensEquation setup)
    (h_power_law : SatisfiesOpticalPowerLaw setup.lens) :
    powerInDiopters setup.lens.opticalPower = 3 ∧
      MatchesAnswerChoice setup.lens.opticalPower .C := by
  have h_reciprocal :=
    reciprocalFocalLengthInCentimeters_eq_three_hundredths setup h_readouts
      h_figure h_eye_plane h_near_point h_thin_lens
  unfold SatisfiesOpticalPowerLaw at h_power_law
  have h_power : powerInDiopters setup.lens.opticalPower = 3 := by
    calc
      powerInDiopters setup.lens.opticalPower =
          100 * (1 / signedFocalLengthInCentimeters setup.lens) := by
            simpa [div_eq_mul_inv] using h_power_law
      _ = 100 * (3 / 100) := by rw [h_reciprocal]
      _ = 3 := by norm_num
  exact ⟨h_power, by
    simpa [MatchesAnswerChoice, displayedPowerInDiopters] using h_power⟩

end PhyXMiniProblems.ProblemPhyXMini0129
