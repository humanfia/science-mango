import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Submission.Kakeya.ConvexFactoring.FrameBoxThickening
import Submission.Kakeya.ConvexGeometry.Tube

/-!
# Explicit frame-box dimensions for closed tubes

This module aligns an orthonormal frame with a tube axis and constructs the
outer box with side lengths `2 * δ`, `2 * δ`, and `1 + 2 * δ`. For
`δ ≤ 1 / 2`, its concentric half-rescaling lies in the tube, yielding a
`HasBoxDimensions 2` certificate. The proofs include the degenerate case
`δ = 0`.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- A unit tube axis can be chosen as the last vector of an orthonormal frame. -/
theorem Tube.exists_alignedFrame {δ : ℝ≥0} (T : Tube δ) :
    ∃ frame : OrthonormalBasis (Fin 3) ℝ Space,
      frame 2 = T.axis.direction := by
  let v : Fin 3 → Space := fun _ => T.axis.direction
  let s : Set (Fin 3) := {2}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact T.axis.norm_direction
  obtain ⟨frame, hframe⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (ι := Fin 3) (by simp [Space])
  refine ⟨frame, ?_⟩
  exact hframe 2 (by simp [s])

/-- Full side lengths of the natural box enclosing a closed `δ`-tube. -/
def Tube.frameBoxSides (δ : ℝ≥0) : Fin 3 → ℝ≥0 :=
  ![2 * δ, 2 * δ, 1 + 2 * δ]

/-- The frame box centered at the midpoint of the tube axis. -/
def Tube.alignedFrameBox {δ : ℝ≥0} (T : Tube δ)
    (frame : OrthonormalBasis (Fin 3) ℝ Space) : FrameBox where
  center := T.axis.base + (2 : ℝ)⁻¹ • T.axis.direction
  frame := frame
  side := Tube.frameBoxSides δ

@[simp] theorem Tube.alignedFrameBox_center {δ : ℝ≥0} (T : Tube δ) (frame) :
    (T.alignedFrameBox frame).center =
      T.axis.base + (2 : ℝ)⁻¹ • T.axis.direction := rfl

@[simp] theorem Tube.alignedFrameBox_frame {δ : ℝ≥0} (T : Tube δ) (frame) :
    (T.alignedFrameBox frame).frame = frame := rfl

@[simp] theorem Tube.alignedFrameBox_side {δ : ℝ≥0} (T : Tube δ) (frame) :
    (T.alignedFrameBox frame).side = Tube.frameBoxSides δ := rfl

/-- The closed tube is contained in its aligned outer frame box. -/
theorem Tube.carrier_subset_alignedFrameBox {δ : ℝ≥0} (T : Tube δ)
    (frame : OrthonormalBasis (Fin 3) ℝ Space)
    (hframe : frame 2 = T.axis.direction) :
    T.carrier ⊆ (T.alignedFrameBox frame).carrier := by
  intro x hx
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (δ : ℝ) by positivity)] at hx
  simp only [mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [T.axis.carrier_eq_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  have hnear (i : Fin 3) :
      |⟪frame i, x⟫_ℝ -
        ⟪frame i, T.axis.base + t • T.axis.direction⟫_ℝ| ≤ (δ : ℝ) :=
    (abs_inner_sub_inner_le_dist_of_norm_eq_one
      (frame i) x (T.axis.base + t • T.axis.direction)
      (frame.norm_eq_one i)).trans hxy
  have hycenter (i : Fin 3) (hi : i ≠ 2) :
      ⟪frame i, T.axis.base + t • T.axis.direction⟫_ℝ =
        ⟪frame i, T.axis.base + (2 : ℝ)⁻¹ • T.axis.direction⟫_ℝ := by
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      ← hframe, frame.inner_eq_zero hi]
    simp
  have htcenter : |t - (2 : ℝ)⁻¹| ≤ (2 : ℝ)⁻¹ := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  have haxis :
      ⟪frame 2, T.axis.base + t • T.axis.direction⟫_ℝ -
          ⟪frame 2, T.axis.base + (2 : ℝ)⁻¹ • T.axis.direction⟫_ℝ =
        t - (2 : ℝ)⁻¹ := by
    rw [hframe, inner_add_right, inner_add_right,
      inner_smul_right, inner_smul_right]
    rw [real_inner_self_eq_norm_sq, T.axis.norm_direction]
    norm_num
  intro i
  fin_cases i
  · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      Tube.alignedFrameBox, Tube.frameBoxSides, hycenter 0 (by decide)]
      using hnear 0
  · simpa [FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      Tube.alignedFrameBox, Tube.frameBoxSides, hycenter 1 (by decide)]
      using hnear 1
  · change |⟪frame 2, x⟫_ℝ -
        ⟪frame 2, T.axis.base + (2 : ℝ)⁻¹ • T.axis.direction⟫_ℝ| ≤
          (((1 + 2 * δ) / 2 : ℝ≥0) : ℝ)
    calc
      _ = |(⟪frame 2, x⟫_ℝ -
            ⟪frame 2, T.axis.base + t • T.axis.direction⟫_ℝ) +
          (t - (2 : ℝ)⁻¹)| := by
            congr 1
            rw [← haxis]
            ring
      _ ≤ |⟪frame 2, x⟫_ℝ -
            ⟪frame 2, T.axis.base + t • T.axis.direction⟫_ℝ| +
          |t - (2 : ℝ)⁻¹| := abs_add_le _ _
      _ ≤ (δ : ℝ) + (2 : ℝ)⁻¹ := add_le_add (hnear 2) htcenter
      _ = (((1 + 2 * δ) / 2 : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_div]
        norm_num
        ring

/-- At scale (1/2), the aligned frame box lies inside the tube when
`δ ≤ 1/2`. The proof is division-free in `δ`, so it includes `δ = 0`. -/
theorem Tube.half_alignedFrameBox_subset_carrier {δ : ℝ≥0} (T : Tube δ)
    (hδ : δ ≤ (2 : ℝ≥0)⁻¹)
    (frame : OrthonormalBasis (Fin 3) ℝ Space)
    (hframe : frame 2 = T.axis.direction) :
    ((T.alignedFrameBox frame).rescale (2 : ℝ≥0)⁻¹).carrier ⊆
      T.carrier := by
  intro x hx
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff] at hx
  let c : Space :=
    T.axis.base + (2 : ℝ)⁻¹ • T.axis.direction
  let d : Fin 3 → ℝ := fun i =>
    ⟪frame i, x⟫_ℝ - ⟪frame i, c⟫_ℝ
  have hd0 : |d 0| ≤ (δ : ℝ) / 2 := by
    simpa [d, c, FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      FrameBox.rescale, Tube.alignedFrameBox, Tube.frameBoxSides,
      NNReal.coe_inv, NNReal.coe_div] using hx (0 : Fin 3)
  have hd1 : |d 1| ≤ (δ : ℝ) / 2 := by
    simpa [d, c, FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      FrameBox.rescale, Tube.alignedFrameBox, Tube.frameBoxSides,
      NNReal.coe_inv, NNReal.coe_div] using hx (1 : Fin 3)
  have hd2 : |d 2| ≤ (1 + 2 * (δ : ℝ)) / 4 := by
    convert hx (2 : Fin 3) using 1 <;>
      simp [d, c, FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      FrameBox.rescale, Tube.alignedFrameBox, Tube.frameBoxSides,
      NNReal.coe_inv, NNReal.coe_div]; ring
  have hδr : (δ : ℝ) ≤ (2 : ℝ)⁻¹ := by
    exact_mod_cast hδ
  have hd2half : |d 2| ≤ (2 : ℝ)⁻¹ :=
    hd2.trans (by norm_num at *; linarith)
  let t : ℝ := (2 : ℝ)⁻¹ + d 2
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    rw [abs_le] at hd2half
    constructor <;> dsimp [t] <;> linarith [hd2half.1, hd2half.2]
  have hsum : ∑ i, d i • frame i = x - c := by
    simpa [d, inner_sub_right] using frame.sum_repr' (x - c)
  have hsum3 :
      d 0 • frame 0 + d 1 • frame 1 + d 2 • frame 2 = x - c := by
    simpa [Fin.sum_univ_three] using hsum
  have hxyvec :
      x - (T.axis.base + t • T.axis.direction) =
        d 0 • frame 0 + d 1 • frame 1 := by
    calc
      x - (T.axis.base + t • T.axis.direction) =
          (x - c) + (c - (T.axis.base + t • T.axis.direction)) := by
            abel
      _ = (d 0 • frame 0 + d 1 • frame 1 + d 2 • frame 2) +
          (c - (T.axis.base + t • T.axis.direction)) := by rw [hsum3]
      _ = d 0 • frame 0 + d 1 • frame 1 := by
        simp only [c, t]
        rw [hframe]
        module
  have hdist :
      dist x (T.axis.base + t • T.axis.direction) ≤ (δ : ℝ) := by
    rw [dist_eq_norm, hxyvec]
    calc
      ‖d 0 • frame 0 + d 1 • frame 1‖ ≤
          ‖d 0 • frame 0‖ + ‖d 1 • frame 1‖ := norm_add_le _ _
      _ = |d 0| + |d 1| := by
        simp [norm_smul, frame.norm_eq_one]
      _ ≤ (δ : ℝ) / 2 + (δ : ℝ) / 2 := add_le_add hd0 hd1
      _ = (δ : ℝ) := by ring
  exact Metric.mem_cthickening_of_dist_le
    x (T.axis.base + t • T.axis.direction) (δ : ℝ) T.axis.carrier
    (T.axis.mem_carrier_of_mem_Icc ht) hdist

/-- A closed tube of radius at most (1/2) has the explicit aligned
`2`-box-dimensions certificate. -/
theorem Tube.hasBoxDimensions_frameBoxSides {δ : ℝ≥0} (T : Tube δ)
    (hδ : δ ≤ (2 : ℝ≥0)⁻¹) :
    HasBoxDimensions 2 (Tube.frameBoxSides δ) T.body := by
  refine ⟨by norm_num, ?_⟩
  obtain ⟨frame, hframe⟩ := T.exists_alignedFrame
  refine ⟨T.alignedFrameBox frame, rfl, ?_, ?_⟩
  · change ((T.alignedFrameBox frame).rescale (2 : ℝ≥0)⁻¹).carrier ⊆
      T.carrier
    exact T.half_alignedFrameBox_subset_carrier hδ frame hframe
  · change T.carrier ⊆ (T.alignedFrameBox frame).carrier
    exact T.carrier_subset_alignedFrameBox frame hframe


end


end Submission.Kakeya.ConvexGeometry
