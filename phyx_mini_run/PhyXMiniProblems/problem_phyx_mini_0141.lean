import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0141

open Dimension

/-!
# Lower edge of a full-body plane mirror

The woman is `1.60 m` tall and her eye is `0.10 m` below her crown.  The
primary figure labels her foot, eye, and crown by `A`, `E`, and `G`; the lower
and upper mirror points by `B` and `F`; the floor point below the mirror by
`D`; and the virtual-image foot and crown by `C` and `H`.

Coordinates below are genuine dimensionful lengths.  Real numbers occur only
after explicitly taking metre readouts, as is appropriate for the numerical
data and the two-dimensional diagram geometry.
-/

/-- A signed physical length, independent of the unit used for its readout. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI units, with the length component made explicitly equal to metres. -/
def metreUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.meters }

/-- The scalar readout of a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length metreUnitChoices).val

/-- A physical point in the vertical plane of the person and mirror. -/
structure DiagramPoint where
  horizontalPosition : LengthQuantity
  verticalPosition : LengthQuantity

/-- The eight point labels visible in the source figure. -/
inductive FigurePoint where
  /-- The woman's foot on the floor. -/
  | A
  /-- The lower edge of the mirror and reflection point for the foot ray. -/
  | B
  /-- The virtual-image foot. -/
  | C
  /-- The point on the floor vertically below the mirror. -/
  | D
  /-- The woman's eye. -/
  | E
  /-- The upper mirror point struck by the crown ray. -/
  | F
  /-- The crown of the woman's head. -/
  | G
  /-- The virtual-image crown. -/
  | H
  deriving DecidableEq, Repr

/-- Solid ray pieces and dashed virtual extensions drawn in the primary image. -/
inductive FigureRayPart where
  | footToLowerMirror
  | lowerMirrorToEye
  | lowerVirtualExtension
  | crownToUpperMirror
  | upperMirrorToEye
  | upperVirtualExtension
  deriving DecidableEq, Repr

/-- Initial endpoint of each labeled ray part in the figure. -/
def FigureRayPart.startPoint : FigureRayPart → FigurePoint
  | .footToLowerMirror => .A
  | .lowerMirrorToEye => .B
  | .lowerVirtualExtension => .B
  | .crownToUpperMirror => .G
  | .upperMirrorToEye => .F
  | .upperVirtualExtension => .F

/-- Final endpoint of each labeled ray part in the figure. -/
def FigureRayPart.endPoint : FigureRayPart → FigurePoint
  | .footToLowerMirror => .B
  | .lowerMirrorToEye => .E
  | .lowerVirtualExtension => .C
  | .crownToUpperMirror => .F
  | .upperMirrorToEye => .E
  | .upperVirtualExtension => .H

/-- The physical point positions and the ray parts shown in the diagram. -/
structure FullBodyPlaneMirrorDiagram where
  position : FigurePoint → DiagramPoint
  rayPartIsShown : FigureRayPart → Prop

/-- Horizontal metre coordinate of a labeled point. -/
def horizontalPositionInMeters
    (diagram : FullBodyPlaneMirrorDiagram) (point : FigurePoint) : ℝ :=
  lengthInMeters (diagram.position point).horizontalPosition

/-- Vertical metre coordinate of a labeled point. -/
def verticalPositionInMeters
    (diagram : FullBodyPlaneMirrorDiagram) (point : FigurePoint) : ℝ :=
  lengthInMeters (diagram.position point).verticalPosition

/-- Two-dimensional metre readout used only for affine diagram geometry. -/
def pointInMeters
    (diagram : FullBodyPlaneMirrorDiagram) (point : FigurePoint) : ℝ × ℝ :=
  (horizontalPositionInMeters diagram point,
    verticalPositionInMeters diagram point)

/-- Signed vertical separation, in metres, from `lower` to `upper`. -/
def verticalSeparationInMeters
    (diagram : FullBodyPlaneMirrorDiagram)
    (lower upper : FigurePoint) : ℝ :=
  verticalPositionInMeters diagram upper -
    verticalPositionInMeters diagram lower

/-!
The numerical measurements stated in the problem.  In particular, this
predicate contains no information about the height of point `B`.
-/
structure MatchesProblemReadouts
    (diagram : FullBodyPlaneMirrorDiagram) : Prop where
  woman_height_metres :
    verticalSeparationInMeters diagram .A .G = 8 / 5
  eye_below_crown_metres :
    verticalSeparationInMeters diagram .E .G = 1 / 10

/-!
Incidence, alignment, ordering, and calibrated readouts visible in the primary
image.  The `1.50 m` arrow is the floor-to-eye segment; together with the
`0.10 m` arrow above it, it agrees with the stated total height `1.60 m`.
No numerical position for the lower mirror edge is recorded here.
-/
structure MatchesPrimaryFigure
    (diagram : FullBodyPlaneMirrorDiagram) : Prop where
  every_depicted_ray_part_is_shown :
    ∀ rayPart, diagram.rayPartIsShown rayPart
  woman_is_vertical_at_A_E_G :
    horizontalPositionInMeters diagram .A =
        horizontalPositionInMeters diagram .E ∧
      horizontalPositionInMeters diagram .E =
        horizontalPositionInMeters diagram .G
  mirror_is_vertical_at_B_D_F :
    horizontalPositionInMeters diagram .B =
        horizontalPositionInMeters diagram .D ∧
      horizontalPositionInMeters diagram .D =
        horizontalPositionInMeters diagram .F
  image_is_vertical_at_C_H :
    horizontalPositionInMeters diagram .C =
      horizontalPositionInMeters diagram .H
  A_C_D_are_on_floor :
    verticalPositionInMeters diagram .A =
        verticalPositionInMeters diagram .D ∧
      verticalPositionInMeters diagram .C =
        verticalPositionInMeters diagram .D
  woman_mirror_image_left_to_right :
    horizontalPositionInMeters diagram .A <
        horizontalPositionInMeters diagram .B ∧
      horizontalPositionInMeters diagram .B <
        horizontalPositionInMeters diagram .C
  eye_height_metres :
    verticalSeparationInMeters diagram .A .E = 3 / 2
  vertical_order_at_person :
    verticalPositionInMeters diagram .A <
        verticalPositionInMeters diagram .E ∧
      verticalPositionInMeters diagram .E <
        verticalPositionInMeters diagram .G
  vertical_order_at_mirror :
    verticalPositionInMeters diagram .D <
        verticalPositionInMeters diagram .B ∧
      verticalPositionInMeters diagram .B <
        verticalPositionInMeters diagram .F

/-!
The virtual-image construction for a vertical plane mirror: image and object
have equal height and equal, opposite horizontal displacement from the mirror.
This is a governing plane-mirror law and does not prescribe the height of the
mirror point.
-/
def IsVirtualImageAcrossVerticalMirror
    (diagram : FullBodyPlaneMirrorDiagram)
    (objectPoint imagePoint : FigurePoint) : Prop :=
  verticalPositionInMeters diagram imagePoint =
      verticalPositionInMeters diagram objectPoint ∧
    horizontalPositionInMeters diagram objectPoint +
        horizontalPositionInMeters diagram imagePoint =
      2 * horizontalPositionInMeters diagram .B

/-!
Ideal plane-mirror optics for the two boundary rays.  The reflected ray to the
eye is collinear with its dashed continuation toward the corresponding virtual
image.  Mathlib's `Collinear` supplies the affine-geometric notion; the
equal-distance clauses supply the physical plane-mirror image law.
-/
structure ObeysIdealPlaneMirrorOptics
    (diagram : FullBodyPlaneMirrorDiagram) : Prop where
  foot_virtual_image :
    IsVirtualImageAcrossVerticalMirror diagram .A .C
  crown_virtual_image :
    IsVirtualImageAcrossVerticalMirror diagram .G .H
  eye_B_C_are_collinear :
    Collinear ℝ
      ({pointInMeters diagram .E, pointInMeters diagram .B,
        pointInMeters diagram .C} : Set (ℝ × ℝ))
  eye_F_H_are_collinear :
    Collinear ℝ
      ({pointInMeters diagram .E, pointInMeters diagram .F,
        pointInMeters diagram .H} : Set (ℝ × ℝ))

/-- The problem measurements imply that the eye is `1.50 m` above the foot. -/
lemma eyeHeight_eq_threeHalves
    (diagram : FullBodyPlaneMirrorDiagram)
    (hProblem : MatchesProblemReadouts diagram) :
    verticalSeparationInMeters diagram .A .E = 3 / 2 := by
  have hHeight := hProblem.woman_height_metres
  have hEyeGap := hProblem.eye_below_crown_metres
  unfold verticalSeparationInMeters at hHeight hEyeGap ⊢
  norm_num at hHeight hEyeGap ⊢
  linarith only [hHeight, hEyeGap]

/-!
At the limiting placement for seeing the feet, the lower edge `B` lies halfway
in height between the eye `E` and the floor.  This is a consequence of the
vertical-mirror image law and the straight virtual sightline, not a setup
assumption.
-/
lemma lowerEdge_bisects_eyeToFloor_height
    (diagram : FullBodyPlaneMirrorDiagram)
    (hFigure : MatchesPrimaryFigure diagram)
    (hOptics : ObeysIdealPlaneMirrorOptics diagram) :
    2 * verticalSeparationInMeters diagram .D .B =
      verticalSeparationInMeters diagram .A .E := by
  let pE := pointInMeters diagram .E
  let pB := pointInMeters diagram .B
  let pC := pointInMeters diagram .C
  have hAE_x := hFigure.woman_is_vertical_at_A_E_G.1
  have hAB_x := hFigure.woman_mirror_image_left_to_right.1
  have hBC_x := hFigure.woman_mirror_image_left_to_right.2
  have hACD_y := hFigure.A_C_D_are_on_floor
  rcases hOptics.foot_virtual_image with ⟨hCA_y, hACB_x⟩
  have hEC : pE ≠ pC := by
    intro h
    have hx :
        horizontalPositionInMeters diagram .E =
          horizontalPositionInMeters diagram .C := by
      simpa [pE, pC, pointInMeters] using congrArg Prod.fst h
    linarith only [hx, hAE_x, hAB_x, hBC_x]
  have hCol := hOptics.eye_B_C_are_collinear
  change Collinear ℝ ({pE, pB, pC} : Set (ℝ × ℝ)) at hCol
  have hB_on_line : pB ∈ line[ℝ, pE, pC] :=
    hCol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hEC
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hB_on_line
  rcases hB_on_line with ⟨t, ht⟩
  rw [AffineMap.lineMap_apply_module'] at ht
  have ht_x :
      t * (horizontalPositionInMeters diagram .C -
          horizontalPositionInMeters diagram .E) +
          horizontalPositionInMeters diagram .E =
        horizontalPositionInMeters diagram .B := by
    simpa [pE, pB, pC, pointInMeters] using congrArg Prod.fst ht
  have ht_y :
      t * (verticalPositionInMeters diagram .C -
          verticalPositionInMeters diagram .E) +
          verticalPositionInMeters diagram .E =
        verticalPositionInMeters diagram .B := by
    simpa [pE, pB, pC, pointInMeters] using congrArg Prod.snd ht
  have hEC_x :
      horizontalPositionInMeters diagram .C -
          horizontalPositionInMeters diagram .E =
        2 * (horizontalPositionInMeters diagram .B -
          horizontalPositionInMeters diagram .E) := by
    linarith only [hAE_x, hACB_x]
  have hEB_pos :
      0 < horizontalPositionInMeters diagram .B -
        horizontalPositionInMeters diagram .E := by
    linarith only [hAE_x, hAB_x]
  have hFactor :
      (horizontalPositionInMeters diagram .B -
          horizontalPositionInMeters diagram .E) * (2 * t - 1) = 0 := by
    calc
      (horizontalPositionInMeters diagram .B -
            horizontalPositionInMeters diagram .E) * (2 * t - 1) =
          t * (2 * (horizontalPositionInMeters diagram .B -
            horizontalPositionInMeters diagram .E)) +
            horizontalPositionInMeters diagram .E -
              horizontalPositionInMeters diagram .B := by ring
      _ = t * (horizontalPositionInMeters diagram .C -
              horizontalPositionInMeters diagram .E) +
            horizontalPositionInMeters diagram .E -
              horizontalPositionInMeters diagram .B := by rw [hEC_x]
      _ = 0 := by linarith only [ht_x]
  have ht_half : t = (1 / 2 : ℝ) := by
    have ht_zero : 2 * t - 1 = 0 :=
      (mul_eq_zero.mp hFactor).resolve_left (ne_of_gt hEB_pos)
    norm_num at ⊢
    linarith only [ht_zero]
  rw [ht_half] at ht_y
  norm_num at ht_y
  unfold verticalSeparationInMeters
  nlinarith only [ht_y, hACD_y.1, hACD_y.2, hCA_y]

/-- The four displayed answer labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Lower-edge height printed beside each answer choice, in metres. -/
def AnswerChoice.lowerEdgeHeightInMeters : AnswerChoice → ℝ
  | .A => 17 / 20
  | .B => 4 / 5
  | .C => 3 / 4
  | .D => 7 / 10

/-- Dataset metadata: the recorded answer is choice C. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The lower edge of the mirror must be `0.75 m` above the floor, i.e. answer C.

Blueprint: `thm:physics:phyx_mini_0141:target`.
-/
theorem lowerMirrorEdgeHeight_eq_threeQuartersMeter
    (diagram : FullBodyPlaneMirrorDiagram)
    (hProblem : MatchesProblemReadouts diagram)
    (hFigure : MatchesPrimaryFigure diagram)
    (hOptics : ObeysIdealPlaneMirrorOptics diagram) :
    verticalSeparationInMeters diagram .D .B = 3 / 4 := by
  have hBisects :=
    lowerEdge_bisects_eyeToFloor_height diagram hFigure hOptics
  have hEyeHeight := eyeHeight_eq_threeHalves diagram hProblem
  norm_num at hEyeHeight ⊢
  linarith only [hBisects, hEyeHeight]

end PhyXMiniProblems.ProblemPhyXMini0141
