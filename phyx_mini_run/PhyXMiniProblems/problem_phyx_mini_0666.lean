import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Area

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0666

open Dimension

/-!
# Curved surface area of a right circular conical frustum

The primary raster shows a conical frustum with two parallel circular bases.
The top-base radius is labelled `r₁`, the larger bottom-base radius is labelled
`r₂`, and the perpendicular separation of the bases is labelled `h`.

Lengths and area are unit-independent Physlib quantities.  Real numbers occur
only at the coherent-SI readout boundary and in the dimensionless coefficients
printed in the answer choices.

Assumption/target split:

* `MatchesSuppliedFrustumFigure` records only labels and geometric features
  visible in image `666.png`;
* `HasValidFrustumParameters` records positivity and the figure-derived radius
  ordering;
* `SatisfiesRightFrustumMeridianGeometry` is the Pythagorean law relating the
  independently stored slant height to `h` and `r₂ - r₁`;
* `SatisfiesFrustumCurvedSurfaceAreaLaw` is the general lateral-area law
  `A = π (r₁ + r₂) l` in terms of that independent slant height; and
* there are no previous-part results.  The eliminated closed formula and the
  unique selection of answer C occur only in `problem_phyx_mini_0666`.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-! ## Primary-figure vocabulary -/

/-- The three dimension labels printed in the supplied diagram. -/
inductive FrustumFigureLabel where
  | r1
  | r2
  | h
  deriving DecidableEq, Fintype, Repr

/-- Named geometric features visible in the supplied frustum diagram. -/
inductive FrustumFigureFeature where
  | topCircularBase
  | bottomCircularBase
  | curvedLateralSurface
  | topRadiusSegment
  | bottomRadiusSegment
  | dashedCentralHeight
  deriving DecidableEq, Fintype, Repr

/-!
Presentation-level evidence transcribed from image `666.png`.  It contains no
surface-area value and no answer-choice selection.
-/
structure SuppliedFrustumFigure where
  labelText : FrustumFigureLabel → String
  showsFeature : FrustumFigureFeature → Bool
  basePlanesAppearParallel : Bool
  heightAppearsPerpendicularToBases : Bool
  topBaseAppearsSmallerThanBottomBase : Bool

/-!
The physical frustum and its independent derived observables.  In particular,
neither `slantHeight` nor `curvedSurfaceArea` is defined from the requested
closed formula.
-/
structure RightCircularConicalFrustum where
  topRadius : LengthQuantity
  bottomRadius : LengthQuantity
  perpendicularHeight : LengthQuantity
  slantHeight : LengthQuantity
  curvedSurfaceArea : DimArea
  figure : SuppliedFrustumFigure

/-! ## Figure readouts and governing geometry -/

/-- Exact transcription of the labels and qualitative geometry in `666.png`. -/
structure MatchesSuppliedFrustumFigure
    (figure : SuppliedFrustumFigure) : Prop where
  topRadiusLabel : figure.labelText FrustumFigureLabel.r1 = "r₁"
  bottomRadiusLabel : figure.labelText FrustumFigureLabel.r2 = "r₂"
  heightLabel : figure.labelText FrustumFigureLabel.h = "h"
  showsTopCircularBase :
    figure.showsFeature FrustumFigureFeature.topCircularBase = true
  showsBottomCircularBase :
    figure.showsFeature FrustumFigureFeature.bottomCircularBase = true
  showsCurvedLateralSurface :
    figure.showsFeature FrustumFigureFeature.curvedLateralSurface = true
  showsTopRadius :
    figure.showsFeature FrustumFigureFeature.topRadiusSegment = true
  showsBottomRadius :
    figure.showsFeature FrustumFigureFeature.bottomRadiusSegment = true
  showsDashedCentralHeight :
    figure.showsFeature FrustumFigureFeature.dashedCentralHeight = true
  parallelBases : figure.basePlanesAppearParallel = true
  perpendicularHeight : figure.heightAppearsPerpendicularToBases = true
  topBaseSmaller : figure.topBaseAppearsSmallerThanBottomBase = true

/-- Positivity and radius ordering for the nondegenerate frustum in the image. -/
structure HasValidFrustumParameters
    (frustum : RightCircularConicalFrustum) : Prop where
  topRadiusPositive : 0 < lengthInMeters frustum.topRadius
  bottomRadiusPositive : 0 < lengthInMeters frustum.bottomRadius
  topRadiusNoLargerThanBottomRadius :
    lengthInMeters frustum.topRadius ≤ lengthInMeters frustum.bottomRadius
  perpendicularHeightPositive : 0 < lengthInMeters frustum.perpendicularHeight
  slantHeightPositive : 0 < lengthInMeters frustum.slantHeight

/-!
Pythagoras applied to a meridian cross-section of a right conical frustum.
This law determines the slant height but does not mention the requested area.
-/
structure SatisfiesRightFrustumMeridianGeometry
    (frustum : RightCircularConicalFrustum) : Prop where
  slantHeightSquared :
    lengthInMeters frustum.slantHeight ^ 2 =
      lengthInMeters frustum.perpendicularHeight ^ 2 +
        (lengthInMeters frustum.bottomRadius -
          lengthInMeters frustum.topRadius) ^ 2

/-!
The general curved-surface-area law for a conical frustum, stated using the
independent physical slant height rather than the answer's eliminated form.
-/
structure SatisfiesFrustumCurvedSurfaceAreaLaw
    (frustum : RightCircularConicalFrustum) : Prop where
  curvedSurfaceAreaLaw :
    areaInSquareMeters frustum.curvedSurfaceArea =
      Real.pi *
        (lengthInMeters frustum.topRadius +
          lengthInMeters frustum.bottomRadius) *
        lengthInMeters frustum.slantHeight

/-! ## Displayed multiple-choice data -/

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless coefficient multiplying the common expression in each option. -/
def answerChoiceCoefficient : AnswerChoice → ℝ
  | .A => 3
  | .B => 2
  | .C => 1
  | .D => 4

/-- Square-metre value of one displayed answer expression. -/
def displayedAnswerValue
    (choice : AnswerChoice) (frustum : RightCircularConicalFrustum) : ℝ :=
  answerChoiceCoefficient choice * Real.pi *
    (lengthInMeters frustum.topRadius +
      lengthInMeters frustum.bottomRadius) *
    Real.sqrt
      (lengthInMeters frustum.perpendicularHeight ^ 2 +
        (lengthInMeters frustum.bottomRadius -
          lengthInMeters frustum.topRadius) ^ 2)

/-!
The curved surface area is option C: `π (r₁ + r₂)` times the meridian slant
length `sqrt (h² + (r₂ - r₁)²)`.  The uniqueness clause also preserves the
multiple-choice conclusion rather than merely restating the numerical formula.
-/
theorem problem_phyx_mini_0666
    (frustum : RightCircularConicalFrustum)
    (hFigure : MatchesSuppliedFrustumFigure frustum.figure)
    (hParameters : HasValidFrustumParameters frustum)
    (hMeridianGeometry : SatisfiesRightFrustumMeridianGeometry frustum)
    (hCurvedSurfaceLaw : SatisfiesFrustumCurvedSurfaceAreaLaw frustum) :
    areaInSquareMeters frustum.curvedSurfaceArea =
        Real.pi *
          (lengthInMeters frustum.topRadius +
            lengthInMeters frustum.bottomRadius) *
          Real.sqrt
            (lengthInMeters frustum.perpendicularHeight ^ 2 +
              (lengthInMeters frustum.bottomRadius -
                lengthInMeters frustum.topRadius) ^ 2) ∧
      (∀ choice : AnswerChoice,
        areaInSquareMeters frustum.curvedSurfaceArea =
            displayedAnswerValue choice frustum ↔
          choice = AnswerChoice.C) := by
  have hSlantHeight :
      lengthInMeters frustum.slantHeight =
        Real.sqrt
          (lengthInMeters frustum.perpendicularHeight ^ 2 +
            (lengthInMeters frustum.bottomRadius -
              lengthInMeters frustum.topRadius) ^ 2) := by
    rw [← hMeridianGeometry.slantHeightSquared]
    exact (Real.sqrt_sq hParameters.slantHeightPositive.le).symm
  have hArea := hCurvedSurfaceLaw.curvedSurfaceAreaLaw
  rw [hSlantHeight] at hArea
  refine ⟨hArea, ?_⟩
  have hRadiusSumPositive :
      0 < lengthInMeters frustum.topRadius +
        lengthInMeters frustum.bottomRadius :=
    add_pos hParameters.topRadiusPositive hParameters.bottomRadiusPositive
  have hCommonPositive :
      0 < Real.pi *
        (lengthInMeters frustum.topRadius +
          lengthInMeters frustum.bottomRadius) *
        Real.sqrt
          (lengthInMeters frustum.perpendicularHeight ^ 2 +
            (lengthInMeters frustum.bottomRadius -
              lengthInMeters frustum.topRadius) ^ 2) := by
    rw [← hSlantHeight]
    exact mul_pos (mul_pos Real.pi_pos hRadiusSumPositive)
      hParameters.slantHeightPositive
  intro choice
  cases choice <;>
    simp only [displayedAnswerValue, answerChoiceCoefficient, reduceCtorEq, iff_false,
      iff_true]
  case A =>
    intro h
    rw [hArea] at h
    nlinarith
  case B =>
    intro h
    rw [hArea] at h
    nlinarith
  case C =>
    rw [hArea]
    ring
  case D =>
    intro h
    rw [hArea] at h
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0666
