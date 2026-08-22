import Submission.Kakeya.ConvexFactoring.TransverseCoordinateOverlap

open scoped ENNReal NNReal Pointwise InnerProductSpace

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-!
# Frame boxes as transverse coordinate windows

This module supplies the one-way geometric bridge from the existing
parallelepiped definition of `FrameBox.carrier` to inner-product coordinate
bounds. It proves that a frame box lies in its three coordinate slabs and in
the corresponding `centeredCoordinateWindow`.

No converse carrier characterization, determinant-angle identity, or
John-ellipsoid assertion is made here.
-/

/-- Inner-product coordinates of the center of a frame box. -/
def FrameBox.coordinateCenter (B : FrameBox) : Coord :=
  fun i ↦ ⟪B.frame i, B.center⟫_ℝ

/-- Half side lengths, indexed in the orthonormal frame. -/
def FrameBox.coordinateHalf (B : FrameBox) : Fin 3 → ℝ≥0 :=
  fun i ↦ B.side i / 2

/-- A point of a frame box has centered frame coordinate
`(t i - 1/2) * side i` for coefficients `t i ∈ [0,1]`. -/
theorem FrameBox.exists_centeredCoordinate_eq
    (B : FrameBox) {x : Space} (hx : x ∈ B.carrier) :
    ∃ t : Fin 3 → ℝ, t ∈ Set.Icc 0 1 ∧
      ∀ i,
        ⟪B.frame i, x⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ =
          (t i - (2 : ℝ)⁻¹) * (B.side i : ℝ) := by
  rcases hx with ⟨y, hy, rfl⟩
  rw [mem_parallelepiped_iff] at hy
  rcases hy with ⟨t, ht, rfl⟩
  refine ⟨t, ht, fun i ↦ ?_⟩
  simp only [FrameBox.corner, FrameBox.edge, inner_add_right, inner_sub_right,
    inner_sum, real_inner_smul_right]
  simp [B.frame.inner_eq_ite]
  ring

/-- Every point of a frame box is within half a side length of its center in
each orthonormal-frame coordinate. -/
theorem FrameBox.centeredCoordinate_abs_le_halfSide
    (B : FrameBox) {x : Space} (hx : x ∈ B.carrier) (i : Fin 3) :
    |⟪B.frame i, x⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ| ≤
      (B.side i : ℝ) / 2 := by
  obtain ⟨t, ht, hcoord⟩ := B.exists_centeredCoordinate_eq hx
  rw [hcoord i, abs_le]
  have ht0 : 0 ≤ t i := ht.1 i
  have ht1 : t i ≤ 1 := ht.2 i
  have hs : 0 ≤ (B.side i : ℝ) := NNReal.zero_le_coe
  constructor <;> norm_num at * <;> nlinarith

/-- A frame box is contained in each of its three coordinate slabs. -/
theorem FrameBox.carrier_subset_affineSlab (B : FrameBox) (i : Fin 3) :
    B.carrier ⊆ affineSlab (B.frame i)
      (B.coordinateCenter i) (B.coordinateHalf i) := by
  intro x hx
  change |⟪B.frame i, x⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ| ≤
    ((B.side i / 2 : ℝ≥0) : ℝ)
  simpa using B.centeredCoordinate_abs_le_halfSide hx i

/-- Simultaneous containment in the three concrete affine slabs. -/
theorem FrameBox.carrier_subset_threeAffineSlabs (B : FrameBox) :
    B.carrier ⊆
      affineSlab (B.frame 0) (B.coordinateCenter 0) (B.coordinateHalf 0) ∩
      affineSlab (B.frame 1) (B.coordinateCenter 1) (B.coordinateHalf 1) ∩
      affineSlab (B.frame 2) (B.coordinateCenter 2) (B.coordinateHalf 2) := by
  intro x hx
  exact ⟨⟨B.carrier_subset_affineSlab 0 hx,
    B.carrier_subset_affineSlab 1 hx⟩,
    B.carrier_subset_affineSlab 2 hx⟩

/-- A frame box is contained in the centered coordinate window determined by
its orthonormal frame and half side lengths. -/
theorem FrameBox.carrier_subset_centeredCoordinateWindow (B : FrameBox) :
    B.carrier ⊆ centeredCoordinateWindow B.frame
      B.coordinateCenter B.coordinateHalf := by
  intro x hx
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  exact B.carrier_subset_affineSlab i hx

/-- The three displayed coordinate slabs form exactly the coordinate window
used in the preceding containment. -/
theorem FrameBox.threeAffineSlabs_eq_centeredCoordinateWindow (B : FrameBox) :
    affineSlab (B.frame 0) (B.coordinateCenter 0) (B.coordinateHalf 0) ∩
      affineSlab (B.frame 1) (B.coordinateCenter 1) (B.coordinateHalf 1) ∩
      affineSlab (B.frame 2) (B.coordinateCenter 2) (B.coordinateHalf 2) =
    centeredCoordinateWindow B.frame B.coordinateCenter B.coordinateHalf := by
  rw [inter_affineSlab_inter_affineSlab_inter_affineSlab]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

end

end Submission.Kakeya.ConvexGeometry
