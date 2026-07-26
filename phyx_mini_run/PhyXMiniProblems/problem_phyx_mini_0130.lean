import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0130

open Dimension

/-!
# Eyeglass power for distant vision in a nearsighted eye

All eye distances and lens focal lengths are signed or unsigned physical
lengths, as appropriate, and optical power has inverse-length dimension.  The
source figure is treated as a schematic distinct from the distant-object ray
configuration: its point `I` is marked at the 12 cm near point, whereas a lens
that corrects distant vision must form a virtual image at the 17 cm far point.
-/

/-- A signed physical length with coherent readouts in every unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical lens power, whose SI readout is measured in diopters. -/
abbrev OpticalPowerQuantity : Type := Dimensionful (WithDim L𝓭⁻¹ ℝ)

/-- The SI scalar readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The SI scalar readout of optical power, in inverse metres (diopters). -/
def powerInDiopters (power : OpticalPowerQuantity) : ℝ :=
  (power UnitChoices.SI).val

/-- Optical type of a paraxial thin lens. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- Whether rays themselves meet at an image or only appear to come from it. -/
inductive ImageKind where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- The four labels whose left-to-right order is visible in the source figure. -/
inductive FigurePoint where
  | O
  | I
  | spectacleLens
  | eye
  deriving DecidableEq, Repr

/--
An object's axial location for the paraxial lens equation.  Optical infinity
is kept as a genuine alternative to a finite physical distance.
-/
inductive ObjectLocation where
  | finite (distanceFromLens : LengthQuantity)
  | opticalInfinity

/-- Object vergence in inverse metres; parallel rays from infinity have zero vergence. -/
def objectVergenceInPerMeters : ObjectLocation → ℝ
  | .finite distance => 1 / lengthInMeters distance
  | .opticalInfinity => 0

/-- The interval of object distances that the unaided eye can focus clearly. -/
structure ClearVisionRange where
  /-- Closest clear object distance, measured from the eye. -/
  nearPointFromEye : LengthQuantity
  /-- Farthest clear object distance, measured from the eye. -/
  farPointFromEye : LengthQuantity

/-- A thin corrective lens with physically distinct focal length and power. -/
structure ThinCorrectiveLens where
  kind : ThinLensKind
  focalLength : LengthQuantity
  opticalPower : OpticalPowerQuantity

/--
The quantities and labels needed to model both the given eye and its spectacle
correction.  The signed distant-image distance is negative when the image lies
on the incoming-light side of the lens.
-/
structure NearsightedCorrectionSetup where
  unaidedRange : ClearVisionRange
  lensToEyeDistance : LengthQuantity
  viewedObject : ObjectLocation
  signedDistantImageDistanceFromLens : LengthQuantity
  distantImageKind : ImageKind
  correctiveLens : ThinCorrectiveLens
  /-- Axial coordinates used only to transcribe the source schematic. -/
  figureAxialPosition : FigurePoint → LengthQuantity
  figureImageKind : ImageKind

/-- The near point, far point, and spectacle-lens offset stated in the problem. -/
def HasStatedDistanceReadouts (setup : NearsightedCorrectionSetup) : Prop :=
  lengthInMeters setup.unaidedRange.nearPointFromEye = 12 / 100 ∧
    lengthInMeters setup.unaidedRange.farPointFromEye = 17 / 100 ∧
    lengthInMeters setup.lensToEyeDistance = 2 / 100

/-- The given eye distances are positive and ordered as a nearsighted range. -/
def HasPhysicalDistanceOrdering (setup : NearsightedCorrectionSetup) : Prop :=
  0 < lengthInMeters setup.lensToEyeDistance ∧
    lengthInMeters setup.lensToEyeDistance <
      lengthInMeters setup.unaidedRange.nearPointFromEye ∧
    lengthInMeters setup.unaidedRange.nearPointFromEye <
      lengthInMeters setup.unaidedRange.farPointFromEye

/--
Primary-image readout: `O`, `I`, the concave spectacle lens, and the eye occur
from left to right.  The dashed backward ray extension identifies `I` as a
virtual image, and the marked `I`--eye separation is the 12 cm near point.
-/
def MatchesSourceFigure (setup : NearsightedCorrectionSetup) : Prop :=
  let x (point : FigurePoint) :=
    lengthInMeters (setup.figureAxialPosition point)
  x .O < x .I ∧
    x .I < x .spectacleLens ∧
    x .spectacleLens < x .eye ∧
    x .eye - x .I =
      lengthInMeters setup.unaidedRange.nearPointFromEye ∧
    setup.figureImageKind = .virtual ∧
    setup.correctiveLens.kind = .diverging

/-- The object whose distant-vision correction is requested is at infinity. -/
def ViewsDistantObject (setup : NearsightedCorrectionSetup) : Prop :=
  setup.viewedObject = .opticalInfinity

/--
Prescription criterion for myopia: the corrective lens makes parallel rays
appear to originate at the unaided far point.  Subtracting the lens-to-eye
offset converts the far-point distance from an eye-based to a lens-based
distance, and the virtual-image sign is negative.
-/
def FormsVirtualImageAtUnaidedFarPoint
    (setup : NearsightedCorrectionSetup) : Prop :=
  setup.distantImageKind = .virtual ∧
    lengthInMeters setup.signedDistantImageDistanceFromLens =
      -(lengthInMeters setup.unaidedRange.farPointFromEye -
        lengthInMeters setup.lensToEyeDistance)

/-- The signed paraxial thin-lens equation `1/f = Vₒ + 1/dᵢ`. -/
def ObeysThinLensEquation (setup : NearsightedCorrectionSetup) : Prop :=
  1 / lengthInMeters setup.correctiveLens.focalLength =
    objectVergenceInPerMeters setup.viewedObject +
      1 / lengthInMeters setup.signedDistantImageDistanceFromLens

/-- Governing relation `P = 1/f` between optical power and focal length. -/
def ObeysOpticalPowerLaw (lens : ThinCorrectiveLens) : Prop :=
  powerInDiopters lens.opticalPower = 1 / lengthInMeters lens.focalLength

/-- The focal-length sign agrees with the physical type of the thin lens. -/
def LensKindAgreesWithFocalSign (lens : ThinCorrectiveLens) : Prop :=
  match lens.kind with
  | .converging => 0 < lengthInMeters lens.focalLength
  | .diverging => lengthInMeters lens.focalLength < 0

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displayed optical-power readout of each answer, in diopters. -/
def answerPowerDiopters : AnswerChoice → ℝ
  | .A => -(53 / 10)
  | .B => -(63 / 10)
  | .C => -(67 / 10)
  | .D => -(56 / 10)

/-- A reported value is an integer number of tenths within half a tenth of the exact value. -/
def IsNearestTenthReadout (exact reported : ℝ) : Prop :=
  (∃ tenths : ℤ, reported = (tenths : ℝ) / 10) ∧
    |exact - reported| ≤ 1 / 20

/-- The required virtual image is 15 cm to the left of the spectacle lens. -/
lemma signedDistantImageDistance_eq_neg_three_twentieth
    (setup : NearsightedCorrectionSetup)
    (h_data : HasStatedDistanceReadouts setup)
    (h_farImage : FormsVirtualImageAtUnaidedFarPoint setup) :
    lengthInMeters setup.signedDistantImageDistanceFromLens = -(3 / 20) := by
  rcases h_data with ⟨_, h_far, h_offset⟩
  rcases h_farImage with ⟨_, h_image⟩
  rw [h_far, h_offset] at h_image
  norm_num at h_image ⊢
  exact h_image

/-- The distant-object lens law fixes the reciprocal focal length at `-20/3 m⁻¹`. -/
lemma reciprocalFocalLength_eq_neg_twenty_thirds
    (setup : NearsightedCorrectionSetup)
    (h_data : HasStatedDistanceReadouts setup)
    (h_distant : ViewsDistantObject setup)
    (h_farImage : FormsVirtualImageAtUnaidedFarPoint setup)
    (h_thinLens : ObeysThinLensEquation setup) :
    1 / lengthInMeters setup.correctiveLens.focalLength = -(20 / 3) := by
  have h_image :=
    signedDistantImageDistance_eq_neg_three_twentieth setup h_data h_farImage
  unfold ViewsDistantObject at h_distant
  unfold ObeysThinLensEquation at h_thinLens
  rw [h_distant, h_image] at h_thinLens
  norm_num [objectVergenceInPerMeters] at h_thinLens ⊢
  exact h_thinLens

/--
The corrective lens has exact optical power `-20/3` diopters.  Rounded to the
nearest tenth, this is `-6.7` diopters, answer choice C.

This formalizes `thm:physics:phyx_mini_0130:target`.
-/
theorem problem_phyx_mini_0130
    (setup : NearsightedCorrectionSetup)
    (h_data : HasStatedDistanceReadouts setup)
    (h_order : HasPhysicalDistanceOrdering setup)
    (h_figure : MatchesSourceFigure setup)
    (h_distant : ViewsDistantObject setup)
    (h_farImage : FormsVirtualImageAtUnaidedFarPoint setup)
    (h_thinLens : ObeysThinLensEquation setup)
    (h_power : ObeysOpticalPowerLaw setup.correctiveLens)
    (h_kind : LensKindAgreesWithFocalSign setup.correctiveLens) :
    powerInDiopters setup.correctiveLens.opticalPower = -(20 / 3) ∧
      IsNearestTenthReadout
        (powerInDiopters setup.correctiveLens.opticalPower)
        (answerPowerDiopters .C) := by
  have h_recip :=
    reciprocalFocalLength_eq_neg_twenty_thirds
      setup h_data h_distant h_farImage h_thinLens
  unfold ObeysOpticalPowerLaw at h_power
  refine ⟨h_power.trans h_recip, ?_⟩
  refine ⟨⟨-67, by norm_num [answerPowerDiopters]⟩, ?_⟩
  rw [h_power, h_recip]
  norm_num [answerPowerDiopters, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0130
