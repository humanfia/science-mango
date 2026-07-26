import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0678

open Dimension

/-!
# Snow-displacement component perpendicular to a ski slope

A ski slope descends to the right at `35°` below the positive horizontal
direction.  A parcel of snow has maximum displacement `1.50 m` along an arrow
that points uphill and is tilted `16°` from the upward vertical.  The supplied
figure asks for the component of this displacement along the outward normal to
the slope.

The maximum displacement and its perpendicular component are unit-independent
Physlib quantities carrying length dimension.  Real numbers are used only for
dimensionless direction vectors, degree readouts, coherent-SI component
readouts, and the values printed beside the answer choices.
-/

/-! ## Dimensionful displacement quantities and planar readouts -/

/-- The two-dimensional Euclidean plane containing the slope and snow arrow. -/
abbrev DiagramPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- A unit-independent planar displacement carrying physical length dimension. -/
abbrev PlanarDisplacementQuantity : Type :=
  Dimensionful (WithDim L𝓭 DiagramPlane)

/-- A signed unit-independent scalar component carrying length dimension. -/
abbrev ScalarLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a planar displacement in coherent SI units, i.e. metres. -/
def displacementVectorInMeters
    (displacement : PlanarDisplacementQuantity) : DiagramPlane :=
  (displacement UnitChoices.SI).val

/-- Read a signed scalar length in coherent SI units, i.e. metres. -/
def lengthInMeters (length : ScalarLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The Euclidean magnitude of a planar displacement's metre readout. -/
def displacementMagnitudeInMeters
    (displacement : PlanarDisplacementQuantity) : ℝ :=
  ‖displacementVectorInMeters displacement‖

/-- Convert a dimensionless angle readout in degrees to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/--
The unit direction at a counterclockwise angle from the positive horizontal
axis. Coordinate `0` is horizontal and coordinate `1` is vertical.
-/
def unitVectorAtAngleDegrees (degrees : ℝ) : DiagramPlane :=
  !₂[Real.cos (degreesToRadians degrees),
      Real.sin (degreesToRadians degrees)]

/-! ## Physical setup and primary-figure labels -/

/-- Named visual features in image `phyx_data/test_image/678.png`. -/
inductive FigureFeature where
  | skier
  | snowCoveredSlope
  | splashedSnowParcel
  | maximumDisplacementArrow
  | dashedVerticalReference
  | horizontalReference
  | slopeAngleArc
  | slopeAngleLabel35
  | verticalAngleArc
  | verticalAngleLabel16
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions distinguished by the problem and its figure. -/
inductive FigureDirection where
  | uphill
  | downhill
  | upwardVertical
  | outwardFromSlope
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative and numerical content of the supplied raster.  The angle
labels are dimensionless degree readouts; the physical displacement is stored
separately in `SkiSlopeDisplacementSetup`.
-/
structure SkiSlopeFigure where
  shows : FigureFeature → Bool
  slopeDescendsToRight : Bool
  snowArrowPoints : FigureDirection
  slopeAngleLabelDegrees : ℝ
  snowAngleFromVerticalLabelDegrees : ℝ

/-!
Independent physical and geometrical quantities for the problem.  The scalar
`perpendicularComponent` is an observable to be determined by the projection
law; no numerical answer is assigned to it here.
-/
structure SkiSlopeDisplacementSetup where
  figure : SkiSlopeFigure
  maximumDisplacement : PlanarDisplacementQuantity
  perpendicularComponent : ScalarLengthQuantity
  slopeAngleFromHorizontalDegrees : ℝ
  snowAngleUphillFromVerticalDegrees : ℝ
  uphillTangentDirection : DiagramPlane
  outwardSurfaceNormalDirection : DiagramPlane

/-! ## Source data, figure evidence, and governing projection law -/

/-!
Problem and primary-image readouts.  Since the slope descends to the right,
its uphill tangent has polar angle `180° - 35°`, while its outward normal has
polar angle `90° - 35°`.  The snow arrow lies left (uphill) of vertical and
therefore has polar angle `90° + 16°`.

This structure fixes only the stated displacement and figure geometry.  It
does not mention the requested perpendicular component or any answer choice.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : SkiSlopeDisplacementSetup) : Prop where
  everyNamedFeatureShown : ∀ feature, setup.figure.shows feature = true
  slopeDescendsToRight : setup.figure.slopeDescendsToRight = true
  snowArrowPointsUphill : setup.figure.snowArrowPoints = .uphill
  printedSlopeAngle : setup.figure.slopeAngleLabelDegrees = 35
  printedSnowAngleFromVertical :
    setup.figure.snowAngleFromVerticalLabelDegrees = 16
  slopeAngleAgreesWithLabel :
    setup.slopeAngleFromHorizontalDegrees =
      setup.figure.slopeAngleLabelDegrees
  snowAngleAgreesWithLabel :
    setup.snowAngleUphillFromVerticalDegrees =
      setup.figure.snowAngleFromVerticalLabelDegrees
  maximumDisplacementMagnitudeMeters :
    displacementMagnitudeInMeters setup.maximumDisplacement = 3 / 2
  uphillTangentGeometry :
    setup.uphillTangentDirection =
      unitVectorAtAngleDegrees
        (180 - setup.slopeAngleFromHorizontalDegrees)
  outwardNormalGeometry :
    setup.outwardSurfaceNormalDirection =
      unitVectorAtAngleDegrees
        (90 - setup.slopeAngleFromHorizontalDegrees)
  snowDisplacementGeometry :
    displacementVectorInMeters setup.maximumDisplacement =
      displacementMagnitudeInMeters setup.maximumDisplacement •
        unitVectorAtAngleDegrees
          (90 + setup.snowAngleUphillFromVerticalDegrees)

/-!
The standard Euclidean law for resolving a displacement perpendicular to a
surface.  The selected outward normal and uphill tangent form an orthonormal
frame, and the signed normal component is their inner-product projection.
This is a general governing relation and contains no requested numerical
value.
-/
structure ObeysPerpendicularProjectionLaw
    (setup : SkiSlopeDisplacementSetup) : Prop where
  uphillTangentIsUnit : ‖setup.uphillTangentDirection‖ = 1
  outwardNormalIsUnit : ‖setup.outwardSurfaceNormalDirection‖ = 1
  tangentOrthogonalToNormal :
    inner ℝ setup.uphillTangentDirection
      setup.outwardSurfaceNormalDirection = 0
  perpendicularComponentIsNormalProjection :
    lengthInMeters setup.perpendicularComponent =
      inner ℝ (displacementVectorInMeters setup.maximumDisplacement)
        setup.outwardSurfaceNormalDirection

/-! ## Exact component and displayed multiple-choice answer -/

/-!
The angle between the arrow and the outward surface normal is
`35° + 16° = 51°`, so the exact perpendicular component is
`1.50 cos 51°` metres.
-/
lemma perpendicularComponent_exact
    (setup : SkiSlopeDisplacementSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_projection : ObeysPerpendicularProjectionLaw setup) :
    lengthInMeters setup.perpendicularComponent =
      (3 / 2 : ℝ) * Real.cos (degreesToRadians (35 + 16)) := by
  rw [h_projection.perpendicularComponentIsNormalProjection,
    h_figure.snowDisplacementGeometry, h_figure.outwardNormalGeometry,
    h_figure.maximumDisplacementMagnitudeMeters]
  simp only [real_inner_smul_left]
  rw [show degreesToRadians (35 + 16) =
      degreesToRadians (90 + setup.snowAngleUphillFromVerticalDegrees) -
        degreesToRadians (90 - setup.slopeAngleFromHorizontalDegrees) by
      rw [h_figure.slopeAngleAgreesWithLabel,
        h_figure.snowAngleAgreesWithLabel, h_figure.printedSlopeAngle,
        h_figure.printedSnowAngleFromVertical]
      norm_num [degreesToRadians]
      all_goals ring]
  rw [Real.cos_sub]
  simp [unitVectorAtAngleDegrees, PiLp.inner_apply, Fin.sum_univ_two]
  all_goals ring

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displacement component, in metres, printed beside each answer label. -/
def displayedComponentInMeters : AnswerChoice → ℝ
  | .A => 89 / 500
  | .B => 851 / 1000
  | .C => 118 / 125
  | .D => 781 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Agreement with a value displayed to three decimal places in metres.  The
half-unit in the last shown digit is `0.0005 m`, avoiding the false assertion
that the rounded decimal is exactly the trigonometric value.
-/
def MatchesDisplayedAnswerToThreeDecimalPlaces
    (setup : SkiSlopeDisplacementSetup) (choice : AnswerChoice) : Prop :=
  |lengthInMeters setup.perpendicularComponent -
      displayedComponentInMeters choice| < 1 / 2000

/-!
The outward normal component is exactly `1.50 cos 51°` metres and agrees,
to the displayed precision, with recorded choice C, `0.944 m`.

Blueprint: `thm:physics:phyx_mini_0678:target`.
-/
theorem problem_phyx_mini_0678
    (setup : SkiSlopeDisplacementSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_projection : ObeysPerpendicularProjectionLaw setup) :
    lengthInMeters setup.perpendicularComponent =
        (3 / 2 : ℝ) * Real.cos (degreesToRadians (35 + 16)) ∧
      MatchesDisplayedAnswerToThreeDecimalPlaces setup recordedAnswerChoice := by
  have h_exact := perpendicularComponent_exact setup h_figure h_projection
  refine ⟨h_exact, ?_⟩
  unfold MatchesDisplayedAnswerToThreeDecimalPlaces
  rw [h_exact]
  norm_num [recordedAnswerChoice, displayedComponentInMeters, degreesToRadians]
  rw [show (51 : ℝ) * Real.pi / 180 =
      Real.pi / 4 + Real.pi / 30 by ring,
    Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]

  have hx_nonneg : 0 ≤ Real.pi / 30 := by positivity
  have hx_abs : |Real.pi / 30| = Real.pi / 30 :=
    abs_of_nonneg hx_nonneg
  have hx_le_one : |Real.pi / 30| ≤ 1 := by
    rw [hx_abs]
    linarith [Real.pi_lt_d6]
  have hcos := Real.cos_bound hx_le_one
  have hsin := Real.sin_bound hx_le_one
  rw [hx_abs] at hcos hsin
  obtain ⟨hcos_lower, hcos_upper⟩ := abs_le.mp hcos
  obtain ⟨hsin_lower, hsin_upper⟩ := abs_le.mp hsin

  have hx_lower : (3.141592 : ℝ) / 30 ≤ Real.pi / 30 := by
    linarith [Real.pi_gt_d6]
  have hx_upper : Real.pi / 30 ≤ (3.141593 : ℝ) / 30 := by
    linarith [Real.pi_lt_d6]
  have hx_lower_nonneg : 0 ≤ (3.141592 : ℝ) / 30 := by norm_num
  have hx_upper_nonneg : 0 ≤ (3.141593 : ℝ) / 30 := by norm_num
  have hx2_lower :
      ((3.141592 : ℝ) / 30) ^ 2 ≤ (Real.pi / 30) ^ 2 := by
    gcongr
  have hx2_upper :
      (Real.pi / 30) ^ 2 ≤ ((3.141593 : ℝ) / 30) ^ 2 := by
    gcongr
  have hx3_lower :
      ((3.141592 : ℝ) / 30) ^ 3 ≤ (Real.pi / 30) ^ 3 := by
    gcongr
  have hx3_upper :
      (Real.pi / 30) ^ 3 ≤ ((3.141593 : ℝ) / 30) ^ 3 := by
    gcongr
  have hx4_upper :
      (Real.pi / 30) ^ 4 ≤ ((3.141593 : ℝ) / 30) ^ 4 := by
    gcongr

  let qLower : ℝ :=
    1 - ((3.141593 : ℝ) / 30) ^ 2 / 2 -
      (3.141593 : ℝ) / 30 +
      ((3.141592 : ℝ) / 30) ^ 3 / 6 -
      2 * (((3.141593 : ℝ) / 30) ^ 4 * (5 / 96))
  let qUpper : ℝ :=
    1 - ((3.141592 : ℝ) / 30) ^ 2 / 2 -
      (3.141592 : ℝ) / 30 +
      ((3.141593 : ℝ) / 30) ^ 3 / 6 +
      2 * (((3.141593 : ℝ) / 30) ^ 4 * (5 / 96))
  have hq_lower :
      qLower ≤ Real.cos (Real.pi / 30) - Real.sin (Real.pi / 30) := by
    dsimp [qLower]
    linarith
  have hq_upper :
      Real.cos (Real.pi / 30) - Real.sin (Real.pi / 30) ≤ qUpper := by
    dsimp [qUpper]
    linarith
  have hq_lower_pos : 0 < qLower := by
    norm_num [qLower]
  have hq_nonneg :
      0 ≤ Real.cos (Real.pi / 30) - Real.sin (Real.pi / 30) :=
    hq_lower_pos.le.trans hq_lower

  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower : (1.414213 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt_upper : Real.sqrt 2 ≤ (1.414214 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hproduct_lower :
      (1.414213 : ℝ) * qLower ≤
        Real.sqrt 2 *
          (Real.cos (Real.pi / 30) - Real.sin (Real.pi / 30)) :=
    mul_le_mul hsqrt_lower hq_lower hq_lower_pos.le
      (Real.sqrt_nonneg (2 : ℝ))
  have hproduct_upper :
      Real.sqrt 2 *
          (Real.cos (Real.pi / 30) - Real.sin (Real.pi / 30)) ≤
        (1.414214 : ℝ) * qUpper :=
    mul_le_mul hsqrt_upper hq_upper hq_nonneg (by norm_num)

  rw [abs_lt]
  constructor <;> norm_num [qLower, qUpper] at hproduct_lower hproduct_upper ⊢
  · linarith
  · linarith

end PhyXMiniProblems.ProblemPhyXMini0678
