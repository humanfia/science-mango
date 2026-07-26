import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0029

open Dimension

/-!
# Optical power of the near-vision segment of a bifocal lens

The eye's near and far points and all optical distances are dimensionful
lengths. The image distance is signed: a virtual image on the object's side of
the lens has a negative SI readout. Optical power has inverse-length dimension,
whose SI readout is measured in inverse metres (diopters).

The supplied figure distinguishes an upper far-vision region from a lower
near-vision region. It contains no numerical geometry beyond those labels.
-/

/-- A signed physical length whose readout changes coherently with unit choice. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical optical power, with dimension inverse length. -/
abbrev DimOpticalPower : Type := Dimensionful (WithDim L𝓭⁻¹ ℝ)

/-- The scalar SI readout of a signed physical length, in metres. -/
def lengthInMeters (length : DimLength) : ℝ :=
  (length UnitChoices.SI).val

/-- The scalar SI readout of optical power, in inverse metres (diopters). -/
def powerInDiopters (power : DimOpticalPower) : ℝ :=
  (power UnitChoices.SI).val

/-- The two physical regions displayed on the bifocal lens. -/
inductive BifocalSegment where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The visual task assigned to a region of the bifocal lens. -/
inductive VisionRole where
  | farVision
  | nearVision
  deriving DecidableEq, Repr

/-- The unaided interval over which the person's eye can focus clearly. -/
structure ClearVisionRange where
  /-- Closest clearly visible object distance from the eye. -/
  nearPoint : DimLength
  /-- Farthest clearly visible object distance from the eye. -/
  farPoint : DimLength

/-- A thin corrective lens with its focal length and optical power. -/
structure ThinCorrectiveLens where
  focalLength : DimLength
  opticalPower : DimOpticalPower

/--
The physical quantities needed to fit the near-vision region of the bifocals.

The problem gives distances from the eye, whereas the thin-lens equation uses
distances from the lens. Both are retained so that the standard negligible
lens-to-eye-distance approximation is stated explicitly rather than hidden.
-/
structure BifocalFitting where
  unaidedRange : ClearVisionRange
  desiredObjectDistanceFromEye : DimLength
  objectDistanceFromLens : DimLength
  signedImageDistanceFromLens : DimLength
  nearCorrectionLens : ThinCorrectiveLens
  correctionSegment : BifocalSegment
  segmentRole : BifocalSegment → VisionRole

/--
The three distance readouts supplied in the problem: near point `30 cm`, far
point `1.5 m`, and desired reading distance `25 cm`.
-/
def HasStatedDistanceReadouts (fitting : BifocalFitting) : Prop :=
  lengthInMeters fitting.unaidedRange.nearPoint = 30 / 100 ∧
    lengthInMeters fitting.unaidedRange.farPoint = 15 / 10 ∧
    lengthInMeters fitting.desiredObjectDistanceFromEye = 25 / 100

/--
The desired object is closer than the unaided near point, and the stated
unaided clear-vision interval is nondegenerate.
-/
def HasPhysicalDistanceOrdering (fitting : BifocalFitting) : Prop :=
  0 < lengthInMeters fitting.desiredObjectDistanceFromEye ∧
    lengthInMeters fitting.desiredObjectDistanceFromEye <
      lengthInMeters fitting.unaidedRange.nearPoint ∧
    lengthInMeters fitting.unaidedRange.nearPoint <
      lengthInMeters fitting.unaidedRange.farPoint

/--
Figure readout: the upper region is for far vision and the lower region is for
near vision; the lens whose power is requested occupies the lower region.
-/
def MatchesBifocalFigure (fitting : BifocalFitting) : Prop :=
  fitting.segmentRole .upper = .farVision ∧
    fitting.segmentRole .lower = .nearVision ∧
    fitting.correctionSegment = .lower

/--
The spectacle lens is modeled at the eye plane, so the object's distance from
the lens equals its stated distance from the eye.
-/
def UsesEyePlaneLensApproximation (fitting : BifocalFitting) : Prop :=
  lengthInMeters fitting.objectDistanceFromLens =
    lengthInMeters fitting.desiredObjectDistanceFromEye

/--
The near-vision lens must place a virtual image at the unaided near point.
Under the Cartesian sign convention this gives a negative image distance.
-/
def FormsVirtualImageAtUnaidedNearPoint (fitting : BifocalFitting) : Prop :=
  lengthInMeters fitting.signedImageDistanceFromLens =
    -lengthInMeters fitting.unaidedRange.nearPoint

/--
The signed thin-lens equation `1/f = 1/dₒ + 1/dᵢ`, written using SI length
readouts. A virtual image has `dᵢ < 0` by the preceding sign convention.
-/
def ObeysThinLensEquation (fitting : BifocalFitting) : Prop :=
  1 / lengthInMeters fitting.nearCorrectionLens.focalLength =
    1 / lengthInMeters fitting.objectDistanceFromLens +
      1 / lengthInMeters fitting.signedImageDistanceFromLens

/-- Governing relation between a thin lens's optical power and focal length. -/
def ObeysOpticalPowerLaw (lens : ThinCorrectiveLens) : Prop :=
  powerInDiopters lens.opticalPower = 1 / lengthInMeters lens.focalLength

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The optical-power readout printed beside each answer choice, in diopters. -/
def answerPowerDiopters : AnswerChoice → ℝ
  | .A => 539 / 1000
  | .B => 517 / 1000
  | .C => 824 / 1000
  | .D => 667 / 1000

/--
`reported` is a three-decimal readout of `exact`: it is an integer number of
thousandths and differs from the exact value by at most half a thousandth.
-/
def IsNearestThousandthReadout (exact reported : ℝ) : Prop :=
  (∃ thousandths : ℤ, reported = (thousandths : ℝ) / 1000) ∧
    |exact - reported| ≤ 1 / 2000

/--
The lens equation and the required virtual-image placement determine the
reciprocal focal length to be exactly `2/3 m⁻¹`.
-/
lemma reciprocalFocalLength_eq_two_thirds
    (fitting : BifocalFitting)
    (h_data : HasStatedDistanceReadouts fitting)
    (h_eyePlane : UsesEyePlaneLensApproximation fitting)
    (h_virtualImage : FormsVirtualImageAtUnaidedNearPoint fitting)
    (h_thinLens : ObeysThinLensEquation fitting) :
    1 / lengthInMeters fitting.nearCorrectionLens.focalLength = 2 / 3 := by
  unfold HasStatedDistanceReadouts at h_data
  unfold UsesEyePlaneLensApproximation at h_eyePlane
  unfold FormsVirtualImageAtUnaidedNearPoint at h_virtualImage
  unfold ObeysThinLensEquation at h_thinLens
  rcases h_data with ⟨h_nearPoint, _, h_desiredDistance⟩
  calc
    1 / lengthInMeters fitting.nearCorrectionLens.focalLength =
        1 / lengthInMeters fitting.objectDistanceFromLens +
          1 / lengthInMeters fitting.signedImageDistanceFromLens := h_thinLens
    _ = 2 / 3 := by
      rw [h_eyePlane, h_desiredDistance, h_virtualImage, h_nearPoint]
      norm_num

/--
The lower near-vision portions of the bifocals require optical power exactly
`+2/3` diopters, whose nearest-thousandth readout is `+0.667` diopters,
answer choice D.

This formalizes `thm:physics:phyx_mini_0029:target`.
-/
theorem problem_phyx_mini_0029
    (fitting : BifocalFitting)
    (h_data : HasStatedDistanceReadouts fitting)
    (h_order : HasPhysicalDistanceOrdering fitting)
    (h_figure : MatchesBifocalFigure fitting)
    (h_eyePlane : UsesEyePlaneLensApproximation fitting)
    (h_virtualImage : FormsVirtualImageAtUnaidedNearPoint fitting)
    (h_thinLens : ObeysThinLensEquation fitting)
    (h_power : ObeysOpticalPowerLaw fitting.nearCorrectionLens) :
    powerInDiopters fitting.nearCorrectionLens.opticalPower = 2 / 3 ∧
      IsNearestThousandthReadout
        (powerInDiopters fitting.nearCorrectionLens.opticalPower)
        (answerPowerDiopters .D) := by
  have h_reciprocal := reciprocalFocalLength_eq_two_thirds fitting h_data
    h_eyePlane h_virtualImage h_thinLens
  unfold ObeysOpticalPowerLaw at h_power
  have h_exactPower :
      powerInDiopters fitting.nearCorrectionLens.opticalPower = 2 / 3 :=
    h_power.trans h_reciprocal
  refine ⟨h_exactPower, ?_⟩
  unfold IsNearestThousandthReadout
  constructor
  · refine ⟨667, ?_⟩
    norm_num [answerPowerDiopters]
  · rw [h_exactPower]
    norm_num [answerPowerDiopters, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0029
