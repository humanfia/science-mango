import Submission.Kakeya.ConvexFactoring.FrameBoxInducedCoveringGrowth
import Submission.Kakeya.ConvexFactoring.CertifiedSlabOverlap

/-!
# Certified local inner boxes and induced-thickening lower bounds

The induced-shading discussion in the source paper needs a comparison of the
volume of a shortest-scale thickening with the portion of that thickening
remaining inside the ambient convex body.  Its stated ball inequality has the
opposite direction from the comparison used in the argument.

A global box-dimensions certificate alone does not give a uniform local
capture fraction at every point.  For example, the convex hull of a
half-rescaled box of dimensions theta by one by one and a long-axis endpoint
still has a fixed-factor box certificate, while its intersection with a
radius-theta ball at that endpoint can have volume of order theta to the
fourth, rather than theta cubed.

This module proves the corresponding certificate-only bridge at the valid
scale.  At each center of a maximal separated packing, the certified inner
frame box is contracted toward that center.  Convexity places the contracted
box in the body, an explicit diameter estimate places it in the packing ball,
and disjointness then gives division-free lower bounds for the body-thickening
intersection.  For a certified slab the explicit contraction theta / 8 gives
a local volume of order theta to the fourth.  No uniform theta-cubed
local-capture conclusion is claimed here.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open FrameBoxInducedCoveringGrowth

noncomputable section

/-- Rescale a frame box toward an arbitrary anchor point. -/
def FrameBox.anchoredRescale (B : FrameBox) (x : Space) (t : ℝ≥0) : FrameBox where
  center := x + (t : ℝ) • (B.center - x)
  frame := B.frame
  side := fun i => t * B.side i

@[simp] theorem FrameBox.anchoredRescale_center
    (B : FrameBox) (x : Space) (t : ℝ≥0) :
    (B.anchoredRescale x t).center = x + (t : ℝ) • (B.center - x) := rfl

@[simp] theorem FrameBox.anchoredRescale_frame
    (B : FrameBox) (x : Space) (t : ℝ≥0) :
    (B.anchoredRescale x t).frame = B.frame := rfl

@[simp] theorem FrameBox.anchoredRescale_side
    (B : FrameBox) (x : Space) (t : ℝ≥0) (i : Fin 3) :
    (B.anchoredRescale x t).side i = t * B.side i := rfl

@[simp] theorem FrameBox.anchoredRescale_edge
    (B : FrameBox) (x : Space) (t : ℝ≥0) (i : Fin 3) :
    (B.anchoredRescale x t).edge i = (t : ℝ) • B.edge i := by
  simp [FrameBox.edge, smul_smul]

@[simp] theorem FrameBox.anchoredRescale_corner
    (B : FrameBox) (x : Space) (t : ℝ≥0) :
    (B.anchoredRescale x t).corner =
      x + (t : ℝ) • (B.corner - x) := by
  simp only [FrameBox.corner, FrameBox.anchoredRescale_center,
    FrameBox.anchoredRescale_edge]
  simp_rw [smul_smul, ← Finset.smul_sum]
  module

/-- Every point of an anchored rescaling is the same convex combination of
the anchor and a point of the original frame box. -/
theorem FrameBox.anchoredRescale_carrier_subset_image
    (B : FrameBox) (x : Space) (t : ℝ≥0) :
    (B.anchoredRescale x t).carrier ⊆
      (fun z => x + (t : ℝ) • (z - x)) '' B.carrier := by
  rw [FrameBox.carrier]
  rintro y ⟨v, hv, rfl⟩
  rw [mem_parallelepiped_iff] at hv
  rcases hv with ⟨u, hu, rfl⟩
  let z : Space := B.corner + ∑ i, u i • B.edge i
  have hz : z ∈ B.carrier := by
    refine ⟨∑ i, u i • B.edge i, ?_, rfl⟩
    rw [mem_parallelepiped_iff]
    exact ⟨u, hu, rfl⟩
  refine ⟨z, hz, ?_⟩
  rw [FrameBox.anchoredRescale_corner]
  dsimp [z]
  simp only [FrameBox.anchoredRescale_edge]
  have hsum :
      (∑ i, u i • (t : ℝ) • B.edge i) =
        (t : ℝ) • ∑ i, u i • B.edge i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_smul]
    congr 1
    ring
  rw [hsum]
  module


/-- Anchored rescaling has the usual cubic volume factor. -/
theorem FrameBox.volume_anchoredRescale
    (B : FrameBox) (x : Space) (t : ℝ≥0) :
    volume (B.anchoredRescale x t).carrier =
      (t : ℝ≥0∞) ^ 3 * volume B.carrier := by
  rw [(B.anchoredRescale x t).volume_carrier, B.volume_carrier]
  simp only [FrameBox.anchoredRescale_side, ENNReal.coe_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- A convenient coarse diameter bound for a frame box. -/
def FrameBox.diameterBound (B : FrameBox) : ℝ≥0 :=
  2 * ∑ i, B.side i

/-- Every point of a frame box is at most the sum of the side lengths from
its center. This deliberately loose bound avoids square roots. -/
theorem FrameBox.dist_center_le_sum_side
    (B : FrameBox) {y : Space} (hy : y ∈ B.carrier) :
    dist y B.center ≤ ((∑ i, B.side i : ℝ≥0) : ℝ) := by
  have hrepr :
      ∑ i, ⟪B.frame i, y - B.center⟫_ℝ • B.frame i = y - B.center :=
    B.frame.sum_repr' (y - B.center)
  have hcoord (i : Fin 3) :
      |⟪B.frame i, y - B.center⟫_ℝ| ≤ (B.side i : ℝ) / 2 := by
    simpa [inner_sub_right] using
      B.centeredCoordinate_abs_le_halfSide hy i
  rw [dist_eq_norm, ← hrepr]
  calc
    ‖∑ i, ⟪B.frame i, y - B.center⟫_ℝ • B.frame i‖ ≤
        ∑ i, ‖⟪B.frame i, y - B.center⟫_ℝ • B.frame i‖ :=
      norm_sum_le _ _
    _ = ∑ i, |⟪B.frame i, y - B.center⟫_ℝ| := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [norm_smul, B.frame.norm_eq_one]
    _ ≤ ∑ i, (B.side i : ℝ) / 2 :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ ≤ ∑ i, (B.side i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact div_le_self (by positivity) (by norm_num)
    _ = ((∑ i, B.side i : ℝ≥0) : ℝ) := by simp

/-- Any two points of a frame box are separated by at most
`diameterBound`. -/
theorem FrameBox.dist_le_diameterBound
    (B : FrameBox) {x y : Space} (hx : x ∈ B.carrier)
    (hy : y ∈ B.carrier) :
    dist x y ≤ (B.diameterBound : ℝ) := by
  have hx' := B.dist_center_le_sum_side hx
  have hy' := B.dist_center_le_sum_side hy
  calc
    dist x y ≤ dist x B.center + dist B.center y := dist_triangle _ _ _
    _ ≤ ((∑ i, B.side i : ℝ≥0) : ℝ) +
        ((∑ i, B.side i : ℝ≥0) : ℝ) := by
      gcongr
      simpa [dist_comm] using hy'
    _ = (B.diameterBound : ℝ) := by
      simp [FrameBox.diameterBound, two_mul]

/-- The certified inner frame box, contracted toward a point of the body. -/
def BoxDimensionsCertificate.localInnerBox
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) (x : Space) (t : ℝ≥0) :
    FrameBox :=
  (cert.box.rescale C⁻¹).anchoredRescale x t

/-- Convexity puts every anchored contraction of the certified inner box
inside the certified body. -/
theorem BoxDimensionsCertificate.localInnerBox_subset_body
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) {x : Space}
    (hx : x ∈ (K : Set Space)) {t : ℝ≥0} (ht : t ≤ 1) :
    (cert.localInnerBox x t).carrier ⊆ (K : Set Space) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ :=
    (cert.box.rescale C⁻¹).anchoredRescale_carrier_subset_image x t hy
  have hzK : z ∈ (K : Set Space) := by
    change z ∈ (cert.box.rescale C⁻¹).body at hz
    exact cert.inner_le hz
  exact K.convex.add_smul_sub_mem hx hzK
    ⟨NNReal.coe_nonneg t, by exact_mod_cast ht⟩

/-- If the contraction factor times the outer-box diameter bound is strictly
smaller than `r`, the local inner box lies in the open packing ball. -/
theorem BoxDimensionsCertificate.localInnerBox_subset_ball
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) {x : Space}
    (hx : x ∈ (K : Set Space)) {t r : ℝ≥0}
    (hfit : (t : ℝ) * (cert.box.diameterBound : ℝ) < (r : ℝ)) :
    (cert.localInnerBox x t).carrier ⊆ Metric.ball x (r : ℝ) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ :=
    (cert.box.rescale C⁻¹).anchoredRescale_carrier_subset_image x t hy
  have hzK : z ∈ (K : Set Space) := by
    change z ∈ (cert.box.rescale C⁻¹).body at hz
    exact cert.inner_le hz
  have hxB : x ∈ cert.box.carrier := by
    change x ∈ cert.box.body
    exact cert.outer_le hx
  have hzB : z ∈ cert.box.carrier := by
    change z ∈ cert.box.body
    exact cert.outer_le hzK
  have hdist := cert.box.dist_le_diameterBound hzB hxB
  rw [Metric.mem_ball]
  calc
    dist (x + (t : ℝ) • (z - x)) x = (t : ℝ) * dist z x := by
      rw [dist_eq_norm]
      have hsub : x + (t : ℝ) • (z - x) - x =
          (t : ℝ) • (z - x) := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg t)]
      rw [dist_eq_norm]
    _ ≤ (t : ℝ) * (cert.box.diameterBound : ℝ) := by
      exact mul_le_mul_of_nonneg_left hdist (NNReal.coe_nonneg t)
    _ < (r : ℝ) := hfit

/-- Exact volume of the local inner box in terms of the certified dimensions. -/
theorem BoxDimensionsCertificate.volume_localInnerBox
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) (x : Space) (t : ℝ≥0) :
    volume (cert.localInnerBox x t).carrier =
      (t : ℝ≥0∞) ^ 3 * (((C⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 3) *
        ∏ i, (side i : ℝ≥0∞) := by
  rw [BoxDimensionsCertificate.localInnerBox,
    FrameBox.volume_anchoredRescale, FrameBox.volume_rescale,
    cert.box.volume_carrier, cert.side_eq]
  ring

/-- The common volume of the local inner boxes used at all packing centers. -/
def BoxDimensionsCertificate.localInnerVolume
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (_cert : BoxDimensionsCertificate C side K) (t : ℝ≥0) : ℝ≥0∞ :=
  (t : ℝ≥0∞) ^ 3 * (((C⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 3) *
    ∏ i, (side i : ℝ≥0∞)

theorem BoxDimensionsCertificate.volume_localInnerBox_eq_localInnerVolume
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) (x : Space) (t : ℝ≥0) :
    volume (cert.localInnerBox x t).carrier =
      cert.localInnerVolume t := by
  exact cert.volume_localInnerBox x t

/-- The local inner boxes at separated packing centers remain pairwise
disjoint because each lies in its corresponding small packing ball. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.localInnerBoxes_pairwiseDisjoint
    {A : Set Space} {r : ℝ≥0}
    (P : PackingCertificate A r)
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (hA : A ⊆ (K : Set Space)) {t : ℝ≥0}
    (hfit : (t : ℝ) * (cert.box.diameterBound : ℝ) < (r : ℝ)) :
    Set.PairwiseDisjoint (↑P.centers : Set Space)
      (fun x => (cert.localInnerBox x t).carrier) := by
  refine P.smallBalls_pairwiseDisjoint.mono_on ?_
  intro x hx
  exact cert.localInnerBox_subset_ball (hA (P.centers_subset hx)) hfit

/-- The union of all local inner boxes lies simultaneously in the certified
body and in the thickening of the packed subset. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.iUnion_localInnerBoxes_subset_body_inter_thickening
    {A : Set Space} {r : ℝ≥0}
    (P : PackingCertificate A r)
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (hA : A ⊆ (K : Set Space)) {t : ℝ≥0} (ht : t ≤ 1)
    (hfit : (t : ℝ) * (cert.box.diameterBound : ℝ) < (r : ℝ)) :
    (⋃ x ∈ P.centers, (cert.localInnerBox x t).carrier) ⊆
      (K : Set Space) ∩ Metric.thickening (r : ℝ) A := by
  refine Set.iUnion₂_subset fun x hx => ?_
  intro y hy
  have hxK : x ∈ (K : Set Space) := hA (P.centers_subset hx)
  constructor
  · exact cert.localInnerBox_subset_body hxK ht hy
  · exact Metric.ball_subset_thickening (P.centers_subset hx) (r : ℝ)
      (cert.localInnerBox_subset_ball hxK hfit hy)

/-- Summing the disjoint local inner boxes gives a genuine lower bound for
the part of the thickening that remains inside the certified convex body. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.card_smul_localInnerVolume_le_body_inter_thickening
    {A : Set Space} {r : ℝ≥0}
    (P : PackingCertificate A r)
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (hA : A ⊆ (K : Set Space)) {t : ℝ≥0} (ht : t ≤ 1)
    (hfit : (t : ℝ) * (cert.box.diameterBound : ℝ) < (r : ℝ)) :
    P.centers.card • cert.localInnerVolume t ≤
      volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) := by
  calc
    P.centers.card • cert.localInnerVolume t =
        ∑ x ∈ P.centers, volume (cert.localInnerBox x t).carrier := by
      simp [cert.volume_localInnerBox_eq_localInnerVolume]
    _ = volume (⋃ x ∈ P.centers, (cert.localInnerBox x t).carrier) := by
      symm
      exact measure_biUnion_finset
        (P.localInnerBoxes_pairwiseDisjoint cert hA hfit)
        (fun x hx => (cert.localInnerBox x t).measurableSet_carrier)
    _ ≤ volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) :=
      measure_mono
        (P.iUnion_localInnerBoxes_subset_body_inter_thickening
          cert hA ht hfit)

/-- Division-free covering growth with the full thickening replaced by its
intersection with the certified body.  The pairwise and local-volume inputs
are derived above rather than assumed. -/
theorem FrameBoxInducedCoveringGrowth.PackingCertificate.volume_mul_localInnerVolume_le_cap_mul_body_inter_thickening
    {A : Set Space} {r : ℝ≥0}
    (P : PackingCertificate A r)
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (hA : A ⊆ (K : Set Space)) (hr : 0 < r)
    {t : ℝ≥0} (ht : t ≤ 1)
    (hfit : (t : ℝ) * (cert.box.diameterBound : ℝ) < (r : ℝ)) :
    volume A * cert.localInnerVolume t ≤
      localBallCap cert.box (3 * r) *
        volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) := by
  have hAbox : A ⊆ cert.box.carrier := by
    intro x hx
    change x ∈ cert.box.body
    exact cert.outer_le (hA hx)
  calc
    volume A * cert.localInnerVolume t ≤
        (P.centers.card • localBallCap cert.box (3 * r)) *
          cert.localInnerVolume t :=
      mul_le_mul_of_nonneg_right
        (P.volume_le_card_smul_localBallCap cert.box hAbox hr) bot_le
    _ = localBallCap cert.box (3 * r) *
        (P.centers.card • cert.localInnerVolume t) := by
      simp only [nsmul_eq_mul]
      ac_rfl
    _ ≤ localBallCap cert.box (3 * r) *
        volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) :=
      mul_le_mul_of_nonneg_left
        (P.card_smul_localInnerVolume_le_body_inter_thickening
          cert hA ht hfit) bot_le

/-- Actual maximal-separated data together with both intersection lower
bounds.  No density or intersection estimate is an input. -/
theorem BoxDimensionsCertificate.exists_packingCertificate_with_bodyIntersectionGrowth
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    {A : Set Space} (hA : A ⊆ (K : Set Space))
    (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) (ht : t ≤ 1)
    (hfit : (t : ℝ) * (cert.box.diameterBound : ℝ) < (r : ℝ)) :
    ∃ P : PackingCertificate A r,
      P.centers.card • cert.localInnerVolume t ≤
          volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) ∧
        volume A * cert.localInnerVolume t ≤
          localBallCap cert.box (3 * r) *
            volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) := by
  have hAbox : A ⊆ cert.box.carrier := by
    intro x hx
    change x ∈ cert.box.body
    exact cert.outer_le (hA hx)
  let P := Classical.choice
    (exists_packingCertificate cert.box hAbox r hr)
  exact ⟨P,
    P.card_smul_localInnerVolume_le_body_inter_thickening
      cert hA ht hfit,
    P.volume_mul_localInnerVolume_le_cap_mul_body_inter_thickening
      cert hA hr ht hfit⟩

theorem SlabDimensionsCertificate.box_diameterBound_le_six
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K) :
    (cert.box.diameterBound : ℝ) ≤ 6 := by
  rw [FrameBox.diameterBound, cert.side_eq, Fin.sum_univ_three]
  have hθ : (θ : ℝ) ≤ 1 := by exact_mod_cast cert.theta_le_one
  simp [slabSides]
  linarith

theorem SlabDimensionsCertificate.theta_div_eight_le_one
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K) :
    θ / 8 ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  push_cast
  have hθ : (θ : ℝ) ≤ 1 := by exact_mod_cast cert.theta_le_one
  linarith [NNReal.coe_nonneg θ]

theorem SlabDimensionsCertificate.theta_div_eight_fits
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K) :
    ((θ / 8 : ℝ≥0) : ℝ) * (cert.box.diameterBound : ℝ) < (θ : ℝ) := by
  have hdiam := cert.box_diameterBound_le_six
  have hθ : 0 < (θ : ℝ) := by exact_mod_cast cert.theta_pos
  have ht : 0 ≤ ((θ / 8 : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  calc
    ((θ / 8 : ℝ≥0) : ℝ) * (cert.box.diameterBound : ℝ) ≤
        ((θ / 8 : ℝ≥0) : ℝ) * 6 :=
      mul_le_mul_of_nonneg_left hdiam ht
    _ < (θ : ℝ) := by
      push_cast
      linarith

theorem SlabDimensionsCertificate.localInnerVolume_theta_div_eight
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K) :
    cert.localInnerVolume (θ / 8) =
      (((θ / 8 : ℝ≥0) : ℝ≥0∞) ^ 3) *
        (((C⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 3) * (θ : ℝ≥0∞) := by
  simp [BoxDimensionsCertificate.localInnerVolume,
    slabSides, Fin.prod_univ_succ]

theorem SlabDimensionsCertificate.localBallCap_three_theta
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K) :
    localBallCap cert.box (3 * θ) =
      (θ : ℝ≥0∞) * (6 * (θ : ℝ≥0∞)) ^ 2 := by
  have hfull :
      (2 : ℝ≥0∞) * (((θ / 2 : ℝ≥0)) : ℝ≥0∞) = (θ : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  unfold localBallCap
  rw [cert.coordinateHalf_shortAxis, hfull]
  push_cast
  ring

theorem SlabDimensionsCertificate.exists_packingCertificate_with_explicit_bodyIntersectionGrowth
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K)
    {A : Set Space} (hA : A ⊆ (K : Set Space)) :
    ∃ P : PackingCertificate A θ,
      P.centers.card •
          ((((θ / 8 : ℝ≥0) : ℝ≥0∞) ^ 3) *
            (((C⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 3) * (θ : ℝ≥0∞)) ≤
        volume ((K : Set Space) ∩ Metric.thickening (θ : ℝ) A) ∧
      volume A *
          ((((θ / 8 : ℝ≥0) : ℝ≥0∞) ^ 3) *
            (((C⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 3) * (θ : ℝ≥0∞)) ≤
        ((θ : ℝ≥0∞) * (6 * (θ : ℝ≥0∞)) ^ 2) *
          volume ((K : Set Space) ∩ Metric.thickening (θ : ℝ) A) := by
  obtain ⟨P, hlow, hgrowth⟩ := cert.toBoxDimensionsCertificate.exists_packingCertificate_with_bodyIntersectionGrowth
    hA θ cert.theta_pos (θ / 8) cert.theta_div_eight_le_one
      cert.theta_div_eight_fits

  refine ⟨P, ?_, ?_⟩
  · simpa [cert.localInnerVolume_theta_div_eight] using hlow
  · rw [cert.localInnerVolume_theta_div_eight,
      cert.localBallCap_three_theta] at hgrowth
    exact hgrowth

end

end Submission.Kakeya.ConvexGeometry
