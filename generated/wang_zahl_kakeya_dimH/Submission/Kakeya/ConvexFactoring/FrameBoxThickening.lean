import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindow

/-!
# Metric thickenings of frame boxes

This module derives widened coordinate-window containment and volume bounds
directly from the open metric thickening definition.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- A real inner-product coordinate with a unit normal is `1`-Lipschitz. -/
theorem abs_inner_sub_inner_le_dist_of_norm_eq_one
    (normal x y : Space) (hnormal : ‖normal‖ = 1) :
    |⟪normal, x⟫_ℝ - ⟪normal, y⟫_ℝ| ≤ dist x y := by
  calc
    |⟪normal, x⟫_ℝ - ⟪normal, y⟫_ℝ| = |⟪normal, x - y⟫_ℝ| := by
      rw [inner_sub_right]
    _ ≤ ‖normal‖ * ‖x - y‖ := abs_real_inner_le_norm normal (x - y)
    _ = dist x y := by
      rw [hnormal, one_mul, dist_eq_norm]

/-- Thickening a set already contained in a unit-normal slab widens its
half-width by the thickening radius. The thickening is open, while the target
slab is closed. The proof also covers the empty source set. -/
theorem thickening_subset_affineSlab_of_subset
    (normal : Space) (hnormal : ‖normal‖ = 1)
    (center : ℝ) (half r : ℝ≥0) (A : Set Space)
    (hA : A ⊆ affineSlab normal center half) :
    Metric.thickening (r : ℝ) A ⊆
      affineSlab normal center (half + r) := by
  intro x hx
  obtain ⟨y, hyA, hxy⟩ := Metric.mem_thickening_iff.mp hx
  have hySlab := hA hyA
  change |⟪normal, y⟫_ℝ - center| ≤ (half : ℝ) at hySlab
  change |⟪normal, x⟫_ℝ - center| ≤ ((half + r : ℝ≥0) : ℝ)
  calc
    |⟪normal, x⟫_ℝ - center| =
        |(⟪normal, x⟫_ℝ - ⟪normal, y⟫_ℝ) +
          (⟪normal, y⟫_ℝ - center)| := by
      congr 1
      ring
    _ ≤ |⟪normal, x⟫_ℝ - ⟪normal, y⟫_ℝ| +
        |⟪normal, y⟫_ℝ - center| := abs_add_le _ _
    _ ≤ dist x y + (half : ℝ) :=
      add_le_add (abs_inner_sub_inner_le_dist_of_norm_eq_one normal x y hnormal)
        hySlab
    _ ≤ (r : ℝ) + (half : ℝ) := by
      linarith
    _ = ((half + r : ℝ≥0) : ℝ) := by
      norm_num
      ring

/-- Exact volume of a coordinate window cut out by an orthonormal basis. -/
theorem volume_centeredCoordinateWindow_orthonormalBasis
    (frame : OrthonormalBasis (Fin 3) ℝ Space)
    (center : Coord) (half : Fin 3 → ℝ≥0) :
    volume (centeredCoordinateWindow frame center half) =
      ∏ i, (2 * (half i : ℝ≥0∞)) := by
  let lower : Coord := fun i => center i - (half i : ℝ)
  let upper : Coord := fun i => center i + (half i : ℝ)
  have hmap :
      innerCoordinateMap (fun i => frame i) =
        frame.repr.toLinearEquiv.toLinearMap := by
    ext x i
    change ⟪frame i, x⟫_ℝ = frame.repr x i
    exact (frame.repr_apply_apply x i).symm
  have hmeas : MeasurableSet (euclideanIcc lower upper) := by
    exact (PiLp.volume_preserving_ofLp (Fin 3)).measurable measurableSet_Icc
  change volume
      ((innerCoordinateMap (fun i => frame i)) ⁻¹'
        euclideanIcc lower upper) = _
  rw [hmap]
  change volume (frame.repr ⁻¹' euclideanIcc lower upper) = _
  rw [frame.measurePreserving_repr.measure_preimage hmeas.nullMeasurableSet]
  rw [volume_euclideanIcc]
  apply Finset.prod_congr rfl
  intro i hi
  change ENNReal.ofReal
      ((center i + (half i : ℝ)) - (center i - (half i : ℝ))) = _
  rw [show center i + (half i : ℝ) - (center i - (half i : ℝ)) =
      2 * (half i : ℝ) by ring]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
  norm_num

/-- Half-widths obtained by widening every frame-box coordinate by `r`. -/
def FrameBox.widenedCoordinateHalf (B : FrameBox) (r : ℝ≥0) : Fin 3 → ℝ≥0 :=
  fun i => B.coordinateHalf i + r

/-- Every coordinate slab containing a frame box also contains the metric
thickening of any subset of that box after widening by `r`. -/
theorem FrameBox.thickening_subset_affineSlab
    (B : FrameBox) (A : Set Space) (hA : A ⊆ B.carrier)
    (r : ℝ≥0) (i : Fin 3) :
    Metric.thickening (r : ℝ) A ⊆
      affineSlab (B.frame i) (B.coordinateCenter i)
        (B.widenedCoordinateHalf r i) := by
  exact thickening_subset_affineSlab_of_subset
    (B.frame i) (B.frame.norm_eq_one i)
    (B.coordinateCenter i) (B.coordinateHalf i) r A
    (hA.trans (B.carrier_subset_affineSlab i))

/-- Simultaneous containment in the three widened coordinate slabs. -/
theorem FrameBox.thickening_subset_threeWidenedAffineSlabs
    (B : FrameBox) (A : Set Space) (hA : A ⊆ B.carrier)
    (r : ℝ≥0) :
    Metric.thickening (r : ℝ) A ⊆
      affineSlab (B.frame 0) (B.coordinateCenter 0)
          (B.widenedCoordinateHalf r 0) ∩
        affineSlab (B.frame 1) (B.coordinateCenter 1)
          (B.widenedCoordinateHalf r 1) ∩
        affineSlab (B.frame 2) (B.coordinateCenter 2)
          (B.widenedCoordinateHalf r 2) := by
  intro x hx
  exact ⟨⟨B.thickening_subset_affineSlab A hA r 0 hx,
    B.thickening_subset_affineSlab A hA r 1 hx⟩,
    B.thickening_subset_affineSlab A hA r 2 hx⟩

/-- The thickening is contained in the single widened coordinate window. -/
theorem FrameBox.thickening_subset_centeredCoordinateWindow
    (B : FrameBox) (A : Set Space) (hA : A ⊆ B.carrier)
    (r : ℝ≥0) :
    Metric.thickening (r : ℝ) A ⊆
      centeredCoordinateWindow B.frame B.coordinateCenter
        (B.widenedCoordinateHalf r) := by
  intro x hx
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  exact B.thickening_subset_affineSlab A hA r i hx

/-- The widened coordinate window has full widths `side i + 2*r`. -/
theorem FrameBox.volume_widenedCoordinateWindow (B : FrameBox) (r : ℝ≥0) :
    volume (centeredCoordinateWindow B.frame B.coordinateCenter
      (B.widenedCoordinateHalf r)) =
      ∏ i, ((B.side i : ℝ≥0∞) + 2 * (r : ℝ≥0∞)) := by
  rw [volume_centeredCoordinateWindow_orthonormalBasis]
  apply Finset.prod_congr rfl
  intro i hi
  have hwidth :
      2 * (B.coordinateHalf i + r) = B.side i + 2 * r := by
    rw [FrameBox.coordinateHalf]
    ring
  exact_mod_cast hwidth

/-- Explicit volume bound for the thickening of any subset of a frame box. -/
theorem FrameBox.volume_thickening_le_prod_side_add_two_mul
    (B : FrameBox) (A : Set Space) (hA : A ⊆ B.carrier)
    (r : ℝ≥0) :
    volume (Metric.thickening (r : ℝ) A) ≤
      ∏ i, ((B.side i : ℝ≥0∞) + 2 * (r : ℝ≥0∞)) := by
  rw [← B.volume_widenedCoordinateWindow r]
  exact measure_mono (B.thickening_subset_centeredCoordinateWindow A hA r)

end

end Submission.Kakeya.ConvexGeometry
