import Submission.Kakeya.ConvexFactoring.CertifiedInducedThickeningLower
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Submission.Kakeya.ConvexFactoring.FrameBoxThickening
import Submission.Kakeya.ConvexFactoring.NeighborhoodInducedShading

/-!
# Buffered packing and induced-carrier growth

A global box-dimensions certificate does not force a shortest-scale ball
centered at an arbitrary point of a convex body to retain a fixed fraction of
its volume inside that body.  The missing local input is therefore represented
explicitly as centerwise ball containment.

A `BufferedPackingCertificate` stores only a genuine separated packing and
the fact that every small packing ball remains in the ambient convex body.  It
does not store any final volume or density estimate.  Disjointness,
measurability of balls, and the previously proved covering cap are used here to
derive division-free ball-volume lower bounds.

The geometric instance is an inset of a frame box.  Coordinate estimates prove
that each radius-`r` ball centered in the inset remains in the original box
when every side has margin `2r`.  This construction is lifted to certified
inner boxes and finally to actual carriers of neighborhood-induced shadings.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open FrameBoxInducedCoveringGrowth
open TransverseCoordinateOverlap

noncomputable section

/-- Points whose open `r`-ball remains in a convex body. -/
def bufferedCore (K : ConvexBody Space) (r : ℝ≥0) : Set Space :=
  {x | Metric.ball x (r : ℝ) ⊆ (K : Set Space)}

@[simp] theorem mem_bufferedCore
    (K : ConvexBody Space) (r : ℝ≥0) (x : Space) :
    x ∈ bufferedCore K r ↔ Metric.ball x (r : ℝ) ⊆ (K : Set Space) :=
  Iff.rfl

/-- A separated packing together with the genuinely local geometric datum
that each small packing ball remains in the ambient convex body. -/
structure BufferedPackingCertificate
    (A : Set Space) (K : ConvexBody Space) (r : ℝ≥0) where
  packing : PackingCertificate A r
  smallBall_subset_body :
    ∀ x ∈ packing.centers, Metric.ball x (r : ℝ) ⊆ (K : Set Space)

/-- A packing of a subset of the buffered core automatically has the required
centerwise local capture. -/
def FrameBoxInducedCoveringGrowth.PackingCertificate.withBuffer
    {A : Set Space} {K : ConvexBody Space} {r : ℝ≥0}
    (P : PackingCertificate A r) (hA : A ⊆ bufferedCore K r) :
    BufferedPackingCertificate A K r where
  packing := P
  smallBall_subset_body := fun _x hx ↦ hA (P.centers_subset hx)

/-- The actual union of small packing balls lies in both the body and the
thickening. -/
theorem BufferedPackingCertificate.iUnion_smallBalls_subset_body_inter_thickening
    {A : Set Space} {K : ConvexBody Space} {r : ℝ≥0}
    (P : BufferedPackingCertificate A K r) :
    (⋃ x ∈ P.packing.centers, Metric.ball x (r : ℝ)) ⊆
      (K : Set Space) ∩ Metric.thickening (r : ℝ) A := by
  refine Set.iUnion₂_subset fun x hx ↦ ?_
  intro y hy
  exact ⟨P.smallBall_subset_body x hx hy,
    Metric.ball_subset_thickening (P.packing.centers_subset hx) (r : ℝ) hy⟩

/-- Disjoint captured balls give a ball-volume-scale lower bound inside the
ambient body. -/
theorem BufferedPackingCertificate.card_smul_ballVolume_le_body_inter_thickening
    {A : Set Space} {K : ConvexBody Space} {r : ℝ≥0}
    (P : BufferedPackingCertificate A K r) :
    P.packing.centers.card • volume (Metric.ball (0 : Space) (r : ℝ)) ≤
      volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) := by
  calc
    P.packing.centers.card • volume (Metric.ball (0 : Space) (r : ℝ)) =
        ∑ x ∈ P.packing.centers, volume (Metric.ball x (r : ℝ)) := by
      simp [InnerProductSpace.volume_ball]
    _ = volume (⋃ x ∈ P.packing.centers, Metric.ball x (r : ℝ)) := by
      symm
      exact measure_biUnion_finset P.packing.smallBalls_pairwiseDisjoint
        (fun _ _ ↦ measurableSet_ball)
    _ ≤ volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) :=
      measure_mono P.iUnion_smallBalls_subset_body_inter_thickening

/-- Combining captured small balls with the proved large-ball covering cap
gives division-free growth inside the ambient body. -/
theorem BufferedPackingCertificate.volume_mul_ballVolume_le_cap_mul_body_inter_thickening
    {A : Set Space} {K : ConvexBody Space} {r : ℝ≥0}
    (P : BufferedPackingCertificate A K r)
    (B : FrameBox) (hA : A ⊆ B.carrier) (hr : 0 < r) :
    volume A * volume (Metric.ball (0 : Space) (r : ℝ)) ≤
      localBallCap B (3 * r) *
        volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) := by
  calc
    volume A * volume (Metric.ball (0 : Space) (r : ℝ)) ≤
        (P.packing.centers.card • localBallCap B (3 * r)) *
          volume (Metric.ball (0 : Space) (r : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (P.packing.volume_le_card_smul_localBallCap B hA hr) bot_le
    _ = localBallCap B (3 * r) *
        (P.packing.centers.card •
          volume (Metric.ball (0 : Space) (r : ℝ))) := by
      simp only [nsmul_eq_mul]
      ac_rfl
    _ ≤ localBallCap B (3 * r) *
        volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) :=
      mul_le_mul_of_nonneg_left
        P.card_smul_ballVolume_le_body_inter_thickening bot_le

/-- A maximal separated packing becomes a buffered packing whenever the
packed set is contained in the buffered core. -/
theorem exists_bufferedPackingCertificate
    (B : FrameBox) {A : Set Space} {K : ConvexBody Space}
    (r : ℝ≥0) (hAbox : A ⊆ B.carrier)
    (hAbuffer : A ⊆ bufferedCore K r) (hr : 0 < r) :
    Nonempty (BufferedPackingCertificate A K r) := by
  exact (exists_packingCertificate B hAbox r hr).map
    (fun P ↦ P.withBuffer hAbuffer)

/-- Actual maximal-separated data and both ball-scale lower bounds. -/
theorem exists_bufferedPackingCertificate_with_growth
    (B : FrameBox) {A : Set Space} {K : ConvexBody Space}
    (r : ℝ≥0) (hAbox : A ⊆ B.carrier)
    (hAbuffer : A ⊆ bufferedCore K r) (hr : 0 < r) :
    ∃ P : BufferedPackingCertificate A K r,
      P.packing.centers.card • volume (Metric.ball (0 : Space) (r : ℝ)) ≤
          volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) ∧
        volume A * volume (Metric.ball (0 : Space) (r : ℝ)) ≤
          localBallCap B (3 * r) *
            volume ((K : Set Space) ∩ Metric.thickening (r : ℝ) A) := by
  let P := Classical.choice
    (exists_bufferedPackingCertificate B r hAbox hAbuffer hr)
  exact ⟨P, P.card_smul_ballVolume_le_body_inter_thickening,
    P.volume_mul_ballVolume_le_cap_mul_body_inter_thickening B hAbox hr⟩

/-- Remove `r` from both faces perpendicular to each frame direction. -/
def FrameBox.inset (B : FrameBox) (r : ℝ≥0) : FrameBox where
  center := B.center
  frame := B.frame
  side := fun i ↦ B.side i - 2 * r

@[simp] theorem FrameBox.inset_center (B : FrameBox) (r : ℝ≥0) :
    (B.inset r).center = B.center := rfl

@[simp] theorem FrameBox.inset_frame (B : FrameBox) (r : ℝ≥0) :
    (B.inset r).frame = B.frame := rfl

@[simp] theorem FrameBox.inset_side (B : FrameBox) (r : ℝ≥0) (i : Fin 3) :
    (B.inset r).side i = B.side i - 2 * r := rfl

/-- An inset frame box remains in the original box, including when truncated
side lengths vanish. -/
theorem FrameBox.inset_carrier_subset_carrier (B : FrameBox) (r : ℝ≥0) :
    (B.inset r).carrier ⊆ B.carrier := by
  intro x hx
  apply B.centeredCoordinateWindow_subset_carrier
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  change |⟪B.frame i, x⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ| ≤
    (B.side i : ℝ) / 2
  have hcoord := (B.inset r).centeredCoordinate_abs_le_halfSide hx i
  simp only [FrameBox.inset_frame, FrameBox.inset_center,
    FrameBox.inset_side] at hcoord
  exact hcoord.trans (div_le_div_of_nonneg_right
    (by exact_mod_cast tsub_le_self) (by norm_num))

/-- If every original side is at least `2r`, the radius-`r` ball around every
point of the inset box remains in the original box. -/
theorem FrameBox.ball_subset_carrier_of_mem_inset
    (B : FrameBox) {r : ℝ≥0} (hside : ∀ i, 2 * r ≤ B.side i)
    {x : Space} (hx : x ∈ (B.inset r).carrier) :
    Metric.ball x (r : ℝ) ⊆ B.carrier := by
  intro y hy
  apply B.centeredCoordinateWindow_subset_carrier
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  change |⟪B.frame i, y⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ| ≤
    (B.side i : ℝ) / 2
  have hxcoord :
      |⟪B.frame i, x⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ| ≤
        (((B.side i - 2 * r : ℝ≥0) : ℝ) / 2) := by
    simpa using (B.inset r).centeredCoordinate_abs_le_halfSide hx i
  have hxy := abs_inner_sub_inner_le_dist_of_norm_eq_one
    (B.frame i) y x (B.frame.norm_eq_one i)
  have hydist : dist y x < (r : ℝ) := Metric.mem_ball.mp hy
  calc
    |⟪B.frame i, y⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ| =
        |(⟪B.frame i, y⟫_ℝ - ⟪B.frame i, x⟫_ℝ) +
          (⟪B.frame i, x⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ)| := by
      congr 1
      ring
    _ ≤ |⟪B.frame i, y⟫_ℝ - ⟪B.frame i, x⟫_ℝ| +
        |⟪B.frame i, x⟫_ℝ - ⟪B.frame i, B.center⟫_ℝ| := abs_add_le _ _
    _ ≤ dist y x + (((B.side i - 2 * r : ℝ≥0) : ℝ) / 2) :=
      add_le_add hxy hxcoord
    _ ≤ (r : ℝ) + (((B.side i - 2 * r : ℝ≥0) : ℝ) / 2) :=
      by exact add_le_add hydist.le le_rfl
    _ = (B.side i : ℝ) / 2 := by
      rw [NNReal.coe_sub (hside i)]
      push_cast
      ring
    _ ≤ (B.side i : ℝ) / 2 := le_rfl

/-- The inset frame box, packaged as a nonempty convex body. -/
def FrameBox.bufferedCoreBody (B : FrameBox) (r : ℝ≥0) : ConvexBody Space :=
  (B.inset r).body

@[simp] theorem FrameBox.coe_bufferedCoreBody (B : FrameBox) (r : ℝ≥0) :
    (B.bufferedCoreBody r : Set Space) = (B.inset r).carrier := rfl

/-- A concrete inset body is contained in the buffered core of every convex
body containing the original frame box. -/
theorem FrameBox.bufferedCoreBody_subset_bufferedCore
    (B : FrameBox) {K : ConvexBody Space} {r : ℝ≥0}
    (hBK : B.carrier ⊆ (K : Set Space))
    (hside : ∀ i, 2 * r ≤ B.side i) :
    (B.bufferedCoreBody r : Set Space) ⊆ bufferedCore K r := by
  intro x hx
  exact (B.ball_subset_carrier_of_mem_inset hside hx).trans hBK

/-- Subsets of the explicit inset body have actual maximal separated
packings whose small balls are captured by `K`. -/
theorem FrameBox.exists_bufferedPackingCertificate_of_subset_bufferedCoreBody
    (B : FrameBox) {K : ConvexBody Space} (r : ℝ≥0) (hr : 0 < r)
    (hBK : B.carrier ⊆ (K : Set Space))
    (hside : ∀ i, 2 * r ≤ B.side i)
    {A : Set Space} (hA : A ⊆ (B.bufferedCoreBody r : Set Space)) :
    Nonempty (BufferedPackingCertificate A K r) := by
  have hAbox : A ⊆ B.carrier :=
    hA.trans (B.inset_carrier_subset_carrier r)
  have hAbuffer : A ⊆ bufferedCore K r :=
    hA.trans (B.bufferedCoreBody_subset_bufferedCore hBK hside)
  exact exists_bufferedPackingCertificate B r hAbox hAbuffer hr

/-- The inset of the certified inner box gives a constructible buffered-core
convex body inside `K`. -/
def BoxDimensionsCertificate.bufferedCoreBody
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) (r : ℝ≥0) : ConvexBody Space :=
  (cert.box.rescale C⁻¹).bufferedCoreBody r

@[simp] theorem BoxDimensionsCertificate.coe_bufferedCoreBody
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) (r : ℝ≥0) :
    (cert.bufferedCoreBody r : Set Space) =
      ((cert.box.rescale C⁻¹).inset r).carrier := rfl

theorem BoxDimensionsCertificate.bufferedCoreBody_subset_bufferedCore
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) {r : ℝ≥0}
    (hside : ∀ i, 2 * r ≤ (cert.box.rescale C⁻¹).side i) :
    (cert.bufferedCoreBody r : Set Space) ⊆ bufferedCore K r := by
  exact (cert.box.rescale C⁻¹).bufferedCoreBody_subset_bufferedCore
    (fun _ hx ↦ cert.inner_le hx) hside

/-- The inset of the certified inner box supplies a concrete buffered maximal
packing for every one of its subsets. -/
theorem BoxDimensionsCertificate.exists_bufferedPackingCertificate_of_subset_bufferedCoreBody
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K) (r : ℝ≥0) (hr : 0 < r)
    (hside : ∀ i, 2 * r ≤ (cert.box.rescale C⁻¹).side i)
    {A : Set Space} (hA : A ⊆ (cert.bufferedCoreBody r : Set Space)) :
    Nonempty (BufferedPackingCertificate A K r) := by
  exact FrameBox.exists_bufferedPackingCertificate_of_subset_bufferedCoreBody
    (cert.box.rescale C⁻¹) r hr
      (fun _ hx ↦ cert.inner_le hx) hside hA

end

end Submission.Kakeya.ConvexGeometry

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth

noncomputable section

namespace ConvexFactorization

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- A centerwise buffer on a fiber turns the generic growth theorem into a
lower bound for the actual neighborhood-induced carrier. -/
theorem exists_bufferedPackingCertificate_with_neighborhoodCarrierGrowth
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ)
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0}
    (cert : BoxDimensionsCertificate C side (W k))
    (r : ℝ≥0) (hr : 0 < r)
    (hbuffer : P.fiberShadedUnion Y k ⊆ bufferedCore (W k) r) :
    ∃ Q : BufferedPackingCertificate (P.fiberShadedUnion Y k) (W k) r,
      Q.packing.centers.card •
          volume (Metric.ball (0 : Space) (r : ℝ)) ≤
        volume ((P.neighborhoodInducedShading Y (r : ℝ)).carrier k) ∧
      volume (P.fiberShadedUnion Y k) *
          volume (Metric.ball (0 : Space) (r : ℝ)) ≤
        FrameBoxInducedCoveringGrowth.localBallCap cert.box (3 * r) *
          volume ((P.neighborhoodInducedShading Y (r : ℝ)).carrier k) := by
  have hAbody := P.fiberShadedUnion_subset_coarseBody Y k
  have hAbox : P.fiberShadedUnion Y k ⊆ cert.box.carrier := by
    intro x hx
    exact cert.outer_le (hAbody hx)
  obtain ⟨Q, hcount, hgrowth⟩ :=
    exists_bufferedPackingCertificate_with_growth cert.box r hAbox hbuffer hr
  refine ⟨Q, ?_, ?_⟩
  · simpa [neighborhoodInducedShading_carrier] using hcount
  · simpa [neighborhoodInducedShading_carrier] using hgrowth

end ConvexFactorization

end


end Submission.Kakeya.ConvexFactoring
