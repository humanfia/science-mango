import Family8Grounding.Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import Family8Grounding.Family8StickyParentHullSupportOnlyV2
import FamilyStickyGrounding.JohnCapturedTubeCertificateCleanAdapterV1
import Mathlib.Tactic

/-!
# Genuine John/plank production for max-owner occurrence hulls

Every quality-selected max-owner hull contains the complete fine tube of its
maximal shaded witness.  Thus a positive fine radius produces a genuine
dimension-three John certificate for that actual hull.  Under the literal
unit-ball support and `rho <= 1`, the hull lies in `B(0,4)`, so its John sides
lie in the explicit interval `[2 * delta, 2304]`.

The final plank statement uses one honest three-side dyadic bucket.  All
members of the retained bucket are normalized by the *same* positive scalar
dilation attached to the common label.  Axis permutations only relabel the
certificate boxes and do not move a body.  In particular, this file never
uses occurrence-specific affine images, which would destroy the actual owner
overlap geometry.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedOccurrenceMaxOwnerHullJohnPlankProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8StickyParentHullSupportOnlyV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)
  (Y : Shading fine.bodyFamily)

/-! ## A genuine John certificate for every actual max-owner hull -/

/-- The complete fine tube of the maximal shaded witness, rather than only
its shading, is contained in the actual parent-specific subhull. -/
theorem occurrenceMaxShadedWitness_tube_subset_maxOwnerHull
    (k : Fin (blocks fine.bodyFamily P).length) :
    (fine.tubes (occurrenceMaxShadedWitness C P Y k)).carrier ⊆
      (occurrenceMaxOwnerHull C P Y k : Set Space) := by
  intro x hx
  apply body_subset_hullContainer fine.bodyFamily
    (show occurrenceMaxShadedWitness C P Y k ∈
      occurrenceMaxOwnerSubfiber C P Y k by
        rw [mem_occurrenceMaxOwnerSubfiber]
        exact ⟨occurrenceMaxShadedWitness_mem C P Y k, rfl⟩)
    (occurrenceMaxOwnerSubfiber_nonempty C P Y k)
  exact hx

/-- Existence of positive-side John data for one genuine max-owner hull. -/
theorem exists_occurrenceMaxOwnerHullJohnData
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) :
    ∃ side : Fin 3 → NNReal,
      (∀ i, 0 < side i) ∧
        Nonempty (BoxDimensionsCertificate 288 side
          (occurrenceMaxOwnerHull C P Y k)) :=
  exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
    (occurrenceMaxOwnerHull C P Y k)
    (fine.tubes (occurrenceMaxShadedWitness C P Y k)) hdelta
    (occurrenceMaxShadedWitness_tube_subset_maxOwnerHull C P Y k)

/-- The actual chosen John side vector. -/
noncomputable def occurrenceMaxOwnerHullJohnSide
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) : Fin 3 → NNReal :=
  Classical.choose (exists_occurrenceMaxOwnerHullJohnData C P Y hdelta k)

/-- The actual chosen John certificate. -/
noncomputable def occurrenceMaxOwnerHullJohnCertificate
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) :
    BoxDimensionsCertificate 288
      (occurrenceMaxOwnerHullJohnSide C P Y hdelta k)
      (occurrenceMaxOwnerHull C P Y k) :=
  Classical.choice
    (Classical.choose_spec
      (exists_occurrenceMaxOwnerHullJohnData C P Y hdelta k)).2

theorem occurrenceMaxOwnerHullJohnSide_pos
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (i : Fin 3) :
    0 < occurrenceMaxOwnerHullJohnSide C P Y hdelta k i :=
  (Classical.choose_spec
    (exists_occurrenceMaxOwnerHullJohnData C P Y hdelta k)).1 i

/-- Put the longest actual John side in coordinate `2`; this changes only
the certificate frame labels, not the convex body. -/
noncomputable def occurrenceMaxOwnerHullLongSide
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) : Fin 3 → NNReal :=
  let side := occurrenceMaxOwnerHullJohnSide C P Y hdelta k
  relabeledSide side (longAxisPermutation side)

noncomputable def occurrenceMaxOwnerHullLongCertificate
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) :
    BoxDimensionsCertificate 288
      (occurrenceMaxOwnerHullLongSide C P Y hdelta k)
      (occurrenceMaxOwnerHull C P Y k) :=
  relabelBoxDimensionsCertificate
    (occurrenceMaxOwnerHullJohnCertificate C P Y hdelta k)
    (longAxisPermutation
      (occurrenceMaxOwnerHullJohnSide C P Y hdelta k))

theorem occurrenceMaxOwnerHullLongSide_pos
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (i : Fin 3) :
    0 < occurrenceMaxOwnerHullLongSide C P Y hdelta k i := by
  exact occurrenceMaxOwnerHullJohnSide_pos C P Y hdelta k _

theorem occurrenceMaxOwnerHullLongSide_le_two
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (i : Fin 3) :
    occurrenceMaxOwnerHullLongSide C P Y hdelta k i ≤
      occurrenceMaxOwnerHullLongSide C P Y hdelta k 2 := by
  exact relabeledSide_le_two
    (occurrenceMaxOwnerHullJohnSide C P Y hdelta k) i

/-- The captured witness tube gives the literal `2*delta` floor in every
coordinate of the relabeled actual John certificate. -/
theorem two_mul_delta_le_occurrenceMaxOwnerHullLongSide
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) (i : Fin 3) :
    2 * delta ≤ occurrenceMaxOwnerHullLongSide C P Y hdelta k i := by
  let j := (longAxisPermutation
    (occurrenceMaxOwnerHullJohnSide C P Y hdelta k)).symm i
  have h := JohnSideLowerFinal.boxCertificate_side_lower_of_tube_subset
    (fine.tubes (occurrenceMaxShadedWitness C P Y k))
    (occurrenceMaxShadedWitness_tube_subset_maxOwnerHull C P Y k)
    (occurrenceMaxOwnerHullJohnCertificate C P Y hdelta k) j
  simpa only [occurrenceMaxOwnerHullLongSide, relabeledSide_apply] using h

/-! ## Explicit support upper bound -/

/-- The actual max-owner hull is supported in `B(0,4)`. -/
theorem occurrenceMaxOwnerHull_subset_closedBall_four
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hrhoOne : rho ≤ 1)
    (k : Fin (blocks fine.bodyFamily P).length) :
    (occurrenceMaxOwnerHull C P Y k : Set Space) ⊆
      Metric.closedBall (0 : Space) 4 := by
  let p : {p // p ∈ C.activeCoarse} :=
    ⟨occurrenceMaxOwner C P Y k,
      occurrenceMaxOwner_mem_activeCoarse C P Y k⟩
  have hp := activeCoarseFamily_body_subset_closedBall_four_of_fine_contained
    fine hfineContained C hrhoOne p
  intro x hx
  apply hp
  exact occurrenceMaxOwnerHull_subset_parent C P Y k hx

/-- Opposite points of the inner John box and the radius-four support give
the uniform raw John-side upper bound `288 * 8 = 2304`. -/
theorem occurrenceMaxOwnerHullJohnSide_le_2304
    (hdelta : 0 < delta)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hrhoOne : rho ≤ 1)
    (k : Fin (blocks fine.bodyFamily P).length) (i : Fin 3) :
    occurrenceMaxOwnerHullJohnSide C P Y hdelta k i ≤ 2304 := by
  let cert := occurrenceMaxOwnerHullJohnCertificate C P Y hdelta k
  let B := cert.box.rescale (288 : NNReal)⁻¹
  have hHull := occurrenceMaxOwnerHull_subset_closedBall_four C P Y
    hfineContained hrhoOne k
  have hxBall : B.positiveFacePoint i ∈ Metric.closedBall (0 : Space) 4 :=
    hHull (cert.inner_le (B.positiveFacePoint_mem_carrier i))
  have hyBall : B.negativeFacePoint i ∈ Metric.closedBall (0 : Space) 4 :=
    hHull (cert.inner_le (B.negativeFacePoint_mem_carrier i))
  have hdistReal :
      dist (B.positiveFacePoint i) (B.negativeFacePoint i) ≤ (8 : Real) := by
    rw [Metric.mem_closedBall] at hxBall hyBall
    calc
      dist (B.positiveFacePoint i) (B.negativeFacePoint i) ≤
          dist (B.positiveFacePoint i) 0 +
            dist 0 (B.negativeFacePoint i) := dist_triangle _ _ _
      _ ≤ 4 + 4 := add_le_add hxBall (by simpa [dist_comm] using hyBall)
      _ = 8 := by norm_num
  rw [B.dist_positiveFacePoint_negativeFacePoint] at hdistReal
  have hdist : B.side i ≤ (8 : NNReal) := by exact_mod_cast hdistReal
  change (288 : NNReal)⁻¹ * cert.box.side i ≤ 8 at hdist
  rw [cert.side_eq] at hdist
  have hscaled :=
    (inv_mul_le_iff₀ (by norm_num : (0 : NNReal) < 288)).1 hdist
  norm_num at hscaled ⊢
  simpa [cert, occurrenceMaxOwnerHullJohnCertificate] using hscaled

theorem occurrenceMaxOwnerHullLongSide_le_2304
    (hdelta : 0 < delta)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hrhoOne : rho ≤ 1)
    (k : Fin (blocks fine.bodyFamily P).length) (i : Fin 3) :
    occurrenceMaxOwnerHullLongSide C P Y hdelta k i ≤ 2304 := by
  exact occurrenceMaxOwnerHullJohnSide_le_2304 C P Y hdelta
    hfineContained hrhoOne k _

/-! ## One common side bucket and one common scalar normalization -/

/-- Long-relabeled John sides on a literal selected occurrence set. -/
noncomputable def selectedOccurrenceMaxOwnerHullLongSide
    (hdelta : 0 < delta)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (k : {k // k ∈ R}) : Fin 3 → NNReal :=
  occurrenceMaxOwnerHullLongSide C P Y hdelta k.1

/-- The explicit cubic ceil-log loss for the interval
`[2*delta,2304]`. -/
def occurrenceMaxOwnerHullSideBucketLoss (delta : NNReal) : Nat :=
  threeSideDyadicLoss ((2 * delta : NNReal) : Real) 2304

theorem selectedOccurrenceMaxOwnerHull_occupiedSideLabels_card_le
    (hdelta : 0 < delta)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hrhoOne : rho ≤ 1)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (occupiedWeightBuckets (Finset.univ : Finset {k // k ∈ R})
      (fun k ↦ sideShapeLabel
        (selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R k))).card ≤
      occurrenceMaxOwnerHullSideBucketLoss delta := by
  apply card_occupied_sideShapeLabel_le
    (lower := ((2 * delta : NNReal) : Real)) (upper := 2304)
  · exact_mod_cast mul_pos (by norm_num : (0 : NNReal) < 2) hdelta
  · intro k _hk i
    constructor
    · exact_mod_cast two_mul_delta_le_occurrenceMaxOwnerHullLongSide
        C P Y hdelta k.1 i
    · exact_mod_cast occurrenceMaxOwnerHullLongSide_le_2304 C P Y hdelta
        hfineContained hrhoOne k.1 i

/-- The common scalar image attached to a side-shape bucket. -/
def occurrenceMaxOwnerHullBucketNormalized
    (label : Fin 3 → Int)
    (k : Fin (blocks fine.bodyFamily P).length) : ConvexBody Space :=
  affineImageConvexBody
    (scalarDilationAffineEquiv
      (sideShapeUpper label 2)⁻¹
      (inv_pos.mpr (sideShapeUpper_pos label 2)))
    (occurrenceMaxOwnerHull C P Y k)

/-- The common scalar image has the actual transported and relabeled John
certificate, not a certificate callback. -/
noncomputable def occurrenceMaxOwnerHullBucketNormalizedCertificate
    (hdelta : 0 < delta) (label : Fin 3 → Int)
    (k : Fin (blocks fine.bodyFamily P).length) :
    BoxDimensionsCertificate 288
      (normalizedBucketSide
        (occurrenceMaxOwnerHullLongSide C P Y hdelta k) label)
      (occurrenceMaxOwnerHullBucketNormalized C P Y label k) := by
  let cert0 := occurrenceMaxOwnerHullLongCertificate C P Y hdelta k
  let cert1 := relabelBoxDimensionsCertificate cert0
    (transverseOrderPermutation label)
  let cert2 := scalarDilationBoxDimensionsCertificate cert1
    (sideShapeUpper label 2)⁻¹
    (inv_pos.mpr (sideShapeUpper_pos label 2))
  have hside :
      (fun i ↦ (sideShapeUpper label 2)⁻¹ *
        relabeledSide (occurrenceMaxOwnerHullLongSide C P Y hdelta k)
          (transverseOrderPermutation label) i) =
        normalizedBucketSide
          (occurrenceMaxOwnerHullLongSide C P Y hdelta k) label :=
    scalarNormalizedRelabeledSide_eq _ _
  exact hside ▸ cert2

theorem occurrenceMaxOwnerHullBucketNormalized_isPlank
    (hdelta : 0 < delta) (label : Fin 3 → Int)
    (k : Fin (blocks fine.bodyFamily P).length)
    (hb : bucketShortB label ≤ 1)
    (hband : ∀ i,
      sideShapeUpper label i / 2 <
          occurrenceMaxOwnerHullLongSide C P Y hdelta k i ∧
        occurrenceMaxOwnerHullLongSide C P Y hdelta k i ≤
          sideShapeUpper label i) :
    IsPlank 576 (bucketShortA label) (bucketShortB label)
      (occurrenceMaxOwnerHullBucketNormalized C P Y label k) := by
  have hwidth := normalizedBucketSide_sideWidthEnvelope hband
  have h := isPlank_of_boxCertificate_sideWidthEnvelope
    (occurrenceMaxOwnerHullBucketNormalizedCertificate C P Y hdelta label k)
    (bucketShortA_pos label) (bucketShortA_le_bucketShortB label) hb hwidth
  simpa only [show (288 : NNReal) * 2 = 576 by norm_num] using h

/-- Actual max-owner hulls have a retained common side bucket.  The loss is
the explicit cubic ceil-log count, and all retained bodies use one common
scalar normalization. -/
theorem exists_occurrenceMaxOwnerHullNormalizedIsPlankBucket_explicitLoss
    (hdelta : 0 < delta)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hrhoOne : rho ≤ 1)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (hR : R.Nonempty)
    (weight : {k // k ∈ R} → Real)
    (hweightNonneg : ∀ k, 0 ≤ weight k) :
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset {k // k ∈ R})
        (fun k ↦ sideShapeLabel
          (selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R k)) ∧
      (∑ k : {k // k ∈ R}, weight k) ≤
        occurrenceMaxOwnerHullSideBucketLoss delta *
          (∑ k ∈ sideShapeBucket Finset.univ
            (selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R) label,
              weight k) ∧
      0 < bucketShortA label ∧
      bucketShortA label ≤ bucketShortB label ∧
      bucketShortB label ≤ 1 ∧
      ∀ k, k ∈ sideShapeBucket Finset.univ
          (selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R) label →
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (occurrenceMaxOwnerHullBucketNormalized C P Y label k.1) := by
  let k0 : {k // k ∈ R} :=
    ⟨Classical.choose hR, Classical.choose_spec hR⟩
  have huniv : (Finset.univ : Finset {k // k ∈ R}).Nonempty :=
    ⟨k0, Finset.mem_univ _⟩
  have hbucket := exists_sideShapeBucket_weight_retention
    (items := (Finset.univ : Finset {k // k ∈ R})) huniv
    (selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R)
    (fun k i ↦ occurrenceMaxOwnerHullLongSide_pos C P Y hdelta k.1 i)
    weight
  obtain ⟨label, hoccupied, hweight, hband⟩ := hbucket
  rcases mem_occupiedWeightBuckets_iff.mp hoccupied with
    ⟨k, _hk, hkLabel⟩
  have hpos : ∀ i, 0 <
      selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R k i :=
    fun i ↦ occurrenceMaxOwnerHullLongSide_pos C P Y hdelta k.1 i
  have h02 := sideShapeUpper_le_of_side_le hpos
    (occurrenceMaxOwnerHullLongSide_le_two C P Y hdelta k.1 0)
  have h12 := sideShapeUpper_le_of_side_le hpos
    (occurrenceMaxOwnerHullLongSide_le_two C P Y hdelta k.1 1)
  rw [hkLabel] at h02 h12
  have hcard := selectedOccurrenceMaxOwnerHull_occupiedSideLabels_card_le
    C P Y hdelta hfineContained hrhoOne R
  have hbucketWeightNonneg : 0 ≤
      ∑ k ∈ sideShapeBucket Finset.univ
        (selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R) label,
          weight k := by
    apply Finset.sum_nonneg
    intro q _hq
    exact hweightNonneg q
  have hcardReal :
      ((occupiedWeightBuckets (Finset.univ : Finset {k // k ∈ R})
        (fun k ↦ sideShapeLabel
          (selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R k))).card :
          Real) ≤ occurrenceMaxOwnerHullSideBucketLoss delta := by
    exact_mod_cast hcard
  have hweightExplicit := hweight.trans (by
    exact mul_le_mul_of_nonneg_right hcardReal hbucketWeightNonneg)
  refine ⟨label, hoccupied, hweightExplicit, bucketShortA_pos label,
    bucketShortA_le_bucketShortB label,
    bucketShortB_le_one label h02 h12, ?_⟩
  intro q hq
  exact occurrenceMaxOwnerHullBucketNormalized_isPlank C P Y hdelta label q.1
    (bucketShortB_le_one label h02 h12) (hband q hq)

#print axioms occurrenceMaxShadedWitness_tube_subset_maxOwnerHull
#print axioms occurrenceMaxOwnerHullJohnCertificate
#print axioms two_mul_delta_le_occurrenceMaxOwnerHullLongSide
#print axioms occurrenceMaxOwnerHullJohnSide_le_2304
#print axioms selectedOccurrenceMaxOwnerHull_occupiedSideLabels_card_le
#print axioms occurrenceMaxOwnerHullBucketNormalizedCertificate
#print axioms occurrenceMaxOwnerHullBucketNormalized_isPlank
#print axioms exists_occurrenceMaxOwnerHullNormalizedIsPlankBucket_explicitLoss

end
end Family8SelectedOccurrenceMaxOwnerHullJohnPlankProducerV1
