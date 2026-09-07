import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV8
import Family8Grounding.Family8StickyParentHullSupportOnlyV2
import Family8Grounding.Family8TubeJohnOuterEllipsoidUnitBallV3
import FamilyStickyGrounding.FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentJohnPlankQuantitativeLossV9

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickyParentHullSupportOnlyV2
open Family8StickyParentHullVolumeBoundV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TubeJohnOuterEllipsoidUnitBallV3
open Family8TubeJohnUnitRescalingV2
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1

noncomputable section

/-! ## A quantitative inverse bound for the winning-hull John map -/

/-- If every John side is at most `M`, the inverse John normalization is
`3*M`-Lipschitz.  The harmless factor three comes from summing the three
orthonormal coordinates; retaining it keeps this bridge independent of a
new operator-norm API. -/
theorem PositiveJohnFrame.symm_dist_le_three_mul_of_side_le
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (M : NNReal)
    (hside : ∀ i, J.side i ≤ M) (y z : Space) :
    dist (J.affineEquiv.symm y) (J.affineEquiv.symm z) ≤
      3 * (M : Real) * dist y z := by
  rw [dist_eq_norm]
  simp only [PositiveJohnFrame.affineEquiv,
    axisEllipsoidNormalizationAffineEquiv_symm_apply]
  have hsub :
      (J.certificate.box.center +
          ∑ i, ((3 * (J.radius i : Real)) *
            ⟪J.certificate.box.frame i, y⟫_Real) •
              J.certificate.box.frame i) -
        (J.certificate.box.center +
          ∑ i, ((3 * (J.radius i : Real)) *
            ⟪J.certificate.box.frame i, z⟫_Real) •
              J.certificate.box.frame i) =
        ∑ i, ((J.side i : Real) *
          ⟪J.certificate.box.frame i, y - z⟫_Real) •
            J.certificate.box.frame i := by
    have hradiusSide (i : Fin 3) :
        (3 : Real) * (J.radius i : Real) = (J.side i : Real) := by
      dsimp only [PositiveJohnFrame.radius]
      norm_num [NNReal.coe_div]
      ring
    simp_rw [hradiusSide]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [inner_sub_right]
    module
  rw [hsub]
  calc
    ‖∑ i, ((J.side i : Real) *
        ⟪J.certificate.box.frame i, y - z⟫_Real) •
          J.certificate.box.frame i‖ ≤
        ∑ i, ‖((J.side i : Real) *
          ⟪J.certificate.box.frame i, y - z⟫_Real) •
            J.certificate.box.frame i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, (M : Real) * ‖y - z‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_smul, J.certificate.box.frame.norm_eq_one, mul_one,
        Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (show (0 : Real) ≤ (J.side i : Real) by positivity)]
      have hsideReal : (J.side i : Real) ≤ (M : Real) := by
        exact_mod_cast hside i
      have hinner := abs_real_inner_le_norm
        (J.certificate.box.frame i) (y - z)
      rw [J.certificate.box.frame.norm_eq_one, one_mul] at hinner
      exact mul_le_mul hsideReal hinner (abs_nonneg _) (by positivity)
    _ = 3 * (M : Real) * ‖y - z‖ := by
      rw [Fin.sum_univ_three]
      ring
    _ = 3 * (M : Real) * dist y z := by rw [dist_eq_norm]

/-! ## The ambient support bounds every winning-hull John side -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Unit-ball support of the fine family and `rho ≤ 1` put the entire
winning hull in `B(0,4)`.  Opposite points of its certified inner John box
then give the explicit upper bound `288 * 8 = 2304` on every John side. -/
theorem selectedParentGreedyBlockJohnSide_le_2304
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) (i : Fin 3) :
    (selectedParentGreedyBlockJohnFrame S hrho P k).side i ≤ 2304 := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let B := J.certificate.box.rescale (288 : NNReal)⁻¹
  have hHull :
      ((blockAt S.activeCoarseFamily P k).body : Set Space) ⊆
        Metric.closedBall (0 : Space) 4 := by
    simpa only [coe_closedBallFourBody] using
      (blockAt_body_subset_of_base S.activeCoarseFamily Finset.univ P
        closedBallFourBody (fun p _hp ↦
          activeCoarseFamily_body_subset_closedBall_four_of_fine_contained
            fine hfineContained S hrhoOne p) k)
  have hxBall : B.positiveFacePoint i ∈ Metric.closedBall (0 : Space) 4 :=
    hHull (J.certificate.inner_le (B.positiveFacePoint_mem_carrier i))
  have hyBall : B.negativeFacePoint i ∈ Metric.closedBall (0 : Space) 4 :=
    hHull (J.certificate.inner_le (B.negativeFacePoint_mem_carrier i))
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
  change (288 : NNReal)⁻¹ * J.certificate.box.side i ≤ 8 at hdist
  rw [J.certificate.side_eq] at hdist
  have hscaled := (inv_mul_le_iff₀ (by norm_num : (0 : NNReal) < 288)).1 hdist
  norm_num at hscaled ⊢
  simpa [J] using hscaled

/-- After the additional positive scalar contraction, the inverse common map
has explicit Lipschitz constant `3*M/r`. -/
theorem contractedJohnAffineEquiv_symm_dist_le
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (M r : NNReal)
    (hr : 0 < r) (hside : ∀ i, J.side i ≤ M) (y z : Space) :
    dist ((contractedJohnAffineEquiv J r hr).symm y)
        ((contractedJohnAffineEquiv J r hr).symm z) ≤
      ((3 * M / r : NNReal) : Real) * dist y z := by
  have hJ := PositiveJohnFrame.symm_dist_le_three_mul_of_side_le J M hside
    ((scalarDilationAffineEquiv r hr).symm y)
    ((scalarDilationAffineEquiv r hr).symm z)
  change dist
      (J.affineEquiv.symm ((scalarDilationAffineEquiv r hr).symm y))
      (J.affineEquiv.symm ((scalarDilationAffineEquiv r hr).symm z)) ≤ _
  calc
    dist
        (J.affineEquiv.symm ((scalarDilationAffineEquiv r hr).symm y))
        (J.affineEquiv.symm ((scalarDilationAffineEquiv r hr).symm z)) ≤
      3 * (M : Real) *
        dist ((scalarDilationAffineEquiv r hr).symm y)
          ((scalarDilationAffineEquiv r hr).symm z) := hJ
    _ = 3 * (M : Real) * ((r : Real)⁻¹ * dist y z) := by
      rw [scalarDilationAffineEquiv_symm_apply,
        scalarDilationAffineEquiv_symm_apply, dist_smul₀,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
          (show (0 : Real) < (r : Real) by exact_mod_cast hr))]
    _ = ((3 * M / r : NNReal) : Real) * dist y z := by
      norm_num [NNReal.coe_div, NNReal.coe_mul]
      ring

/-! ## A round inner ball survives the common affine normalization -/

/-- Every selected actual coarse parent contains a common-scale round ball
after the winning-hull John map and scalar contraction.  The center may
vary with the parent, but the radius `r*rho/6912` is uniform on the block. -/
theorem selectedParentContracted_closedBall_subset
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}) :
    let J := selectedParentGreedyBlockJohnFrame S hrho P k
    let e := contractedJohnAffineEquiv J r hr
    let T := S.coarse.tubes p.1.1
    Metric.closedBall (e T.axis.base)
        (((r * rho / 6912 : NNReal) : Real)) ⊆
      (selectedParentAffineFamily e S
        (blockAt S.activeCoarseFamily P k).fiber p : Set Space) := by
  dsimp only
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let T := S.coarse.tubes p.1.1
  have hJside : ∀ i, J.side i ≤ (2304 : NNReal) := by
    intro i
    exact selectedParentGreedyBlockJohnSide_le_2304
      hfineContained S hrho hrhoOne P k i
  intro y hy
  rw [selectedParentAffineFamily_apply]
  change y ∈ e '' T.carrier
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  apply Metric.closedBall_subset_cthickening T.axis.base_mem_carrier
  rw [Metric.mem_closedBall]
  rw [Metric.mem_closedBall] at hy
  have hinverse := contractedJohnAffineEquiv_symm_dist_le
    J 2304 r hr hJside y (e T.axis.base)
  calc
    dist (e.symm y) T.axis.base =
        dist (e.symm y) (e.symm (e T.axis.base)) := by
          rw [e.symm_apply_apply]
    _ ≤ ((3 * (2304 : NNReal) / r : NNReal) : Real) *
        dist y (e T.axis.base) := hinverse
    _ ≤ ((3 * (2304 : NNReal) / r : NNReal) : Real) *
        (((r * rho / 6912 : NNReal) : Real)) := by
          exact mul_le_mul_of_nonneg_left hy (by positivity)
    _ = (rho : Real) := by
      norm_num [NNReal.coe_div, NNReal.coe_mul]
      field_simp [show (r : Real) ≠ 0 by exact_mod_cast hr.ne']

/-! ## Uniform quantitative floors for actual member John sides -/

/-- The uniform side floor forced by the transported coarse-tube ball. -/
def selectedParentSideFloor (rho r : NNReal) : NNReal :=
  r * rho / 3456
theorem selectedParentSideFloor_pos {r : NNReal}
    (hrho : 0 < rho) (hr : 0 < r) :
    0 < selectedParentSideFloor rho r := by
  exact div_pos (mul_pos hr hrho) (by norm_num)

/-- Every coordinate of the automatically chosen member John certificate has
the explicit floor `r*rho/3456`; no side-floor premise is accepted. -/
theorem selectedParentContractedJohnSide_floor
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
    (i : Fin 3) :
    selectedParentSideFloor rho r ≤
      selectedParentAffineJohnSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p i := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let T := S.coarse.tubes p.1.1
  have hball :
      Metric.closedBall (e T.axis.base)
          (((r * rho / 6912 : NNReal) : Real)) ⊆
        (selectedParentAffineFamily e S
          (blockAt S.activeCoarseFamily P k).fiber p : Set Space) := by
    simpa [J, e, T] using
      (selectedParentContracted_closedBall_subset
        hfineContained S hrho hrhoOne P k r hr p)
  have hlower := boxCertificate_side_lower_of_closedBall_subset
    (e T.axis.base) hball
    (selectedParentAffineJohnCertificate e S
      (blockAt S.activeCoarseFamily P k).fiber hrho p) i
  have hfloor :
      2 * (r * rho / 6912) = selectedParentSideFloor rho r := by
    apply NNReal.eq
    norm_num [selectedParentSideFloor, NNReal.coe_div, NNReal.coe_mul]
    ring
  simpa [J, e, T, hfloor] using hlower

/-- Long-axis relabeling is carrier preserving, so the same floor holds in
all three relabeled coordinates used by V7 and V8. -/
theorem selectedParentContractedLongRelabeledSide_floor
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
    (i : Fin 3) :
    selectedParentSideFloor rho r ≤
      selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p i := by
  simp only [selectedParentLongRelabeledSide, relabeledSide_apply]
  exact selectedParentContractedJohnSide_floor
    hfineContained S hrho hrhoOne P k r hr p _

/-! ## Three-coordinate dyadic label counting -/

/-- Explicit number of integer dyadic triples between one positive lower
scale and one common upper scale. -/
def threeSideDyadicLoss (lower upper : Real) : Nat :=
  ((dyadicCeilBucket upper + 1 - dyadicCeilBucket lower).toNat) ^ 3

/-- If all three positive sides lie in `[lower,upper]`, the occupied shape
labels fit in the literal product of three integer intervals. -/
theorem card_occupied_sideShapeLabel_le
    {item : Type*} [DecidableEq item]
    (items : Finset item) (side : item → Fin 3 → NNReal)
    {lower upper : Real} (hlower : 0 < lower)
    (hside : ∀ x, x ∈ items → ∀ i,
      lower ≤ (side x i : Real) ∧ (side x i : Real) ≤ upper) :
    (occupiedWeightBuckets items
      (fun x ↦ sideShapeLabel (side x))).card ≤
        threeSideDyadicLoss lower upper := by
  let labels : Finset (Fin 3 → Int) :=
    Fintype.piFinset (fun _i : Fin 3 ↦
      Finset.Icc (dyadicCeilBucket lower) (dyadicCeilBucket upper))
  have hsubset :
      occupiedWeightBuckets items (fun x ↦ sideShapeLabel (side x)) ⊆
        labels := by
    intro label hlabel
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    rcases mem_occupiedWeightBuckets_iff.mp hlabel with ⟨x, hx, rfl⟩
    have hxi := hside x hx i
    change dyadicCeilBucket lower ≤ dyadicCeilBucket (side x i : Real) ∧
      dyadicCeilBucket (side x i : Real) ≤ dyadicCeilBucket upper
    exact ⟨dyadicCeilBucket_mono hlower hxi.1,
      dyadicCeilBucket_mono (hlower.trans_le hxi.1) hxi.2⟩
  calc
    (occupiedWeightBuckets items
        (fun x ↦ sideShapeLabel (side x))).card ≤ labels.card :=
      Finset.card_le_card hsubset
    _ = threeSideDyadicLoss lower upper := by
      dsimp only [labels]
      rw [Fintype.card_piFinset]
      simp_rw [Int.card_Icc]
      rw [Fin.prod_univ_three]
      simp only [threeSideDyadicLoss]
      ring

/-- The literal three-coordinate dyadic loss for the actual selected-parent
side interval `[r*rho/3456, 1728*r]`. -/
def selectedParentSideBucketLoss (rho r : NNReal) : Nat :=
  threeSideDyadicLoss (selectedParentSideFloor rho r : Real)
    ((1728 * r : NNReal) : Real)

/-- The actual occupied side-label set has an explicit finite cubic
ceil-log bound. -/
theorem selectedParent_occupiedSideShapeLabels_card_le
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let side : parent → Fin 3 → NNReal := fun p ↦
      selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p
    (occupiedWeightBuckets (Finset.univ : Finset parent)
      (fun p ↦ sideShapeLabel (side p))).card ≤
        selectedParentSideBucketLoss rho r := by
  dsimp only
  apply card_occupied_sideShapeLabel_le
    (lower := (selectedParentSideFloor rho r : Real))
    (upper := ((1728 * r : NNReal) : Real))
  · exact_mod_cast selectedParentSideFloor_pos hrho hr
  · intro p _hp i
    constructor
    · exact_mod_cast selectedParentContractedLongRelabeledSide_floor
        hfineContained S hrho hrhoOne P k r hr p i
    · exact_mod_cast selectedParentContractedLongRelabeledSide_le
        S hrho P k r hr p i

/-! ## V8 consumption with the explicit quantitative loss -/

/-- Under the paper's ambient support, V8's exact occupied-card loss is
replaced by the explicit cubic ceil-log loss.  Nonnegativity is the natural
condition needed to enlarge a weighted pigeonhole factor. -/
theorem exists_selectedParentActualIsPlankBucket_explicitLoss
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (weight :
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} → Real)
    (hweightNonneg : ∀ p, 0 ≤ weight p) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let side : parent → Fin 3 → NNReal := fun p ↦
      selectedParentLongRelabeledSide e S
        (blockAt S.activeCoarseFamily P k).fiber hrho p
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p ↦ sideShapeLabel (side p)) ∧
      (∑ p : parent, weight p) ≤
        selectedParentSideBucketLoss rho r *
          (∑ p ∈ sideShapeBucket Finset.univ side label, weight p) ∧
      0 < bucketShortA label ∧
      bucketShortA label ≤ bucketShortB label ∧
      bucketShortB label ≤ 1 ∧
      ∀ p, p ∈ sideShapeBucket Finset.univ side label →
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S
            (blockAt S.activeCoarseFamily P k).fiber p) := by
  dsimp only
  have hbucket :=
    exists_selectedParentActualIsPlankBucket_weight_retention
      S hrho P k r hr weight
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  have hcard := selectedParent_occupiedSideShapeLabels_card_le
    hfineContained S hrho hrhoOne P k r hr
  dsimp only at hcard
  have hbucketNonneg :
      0 ≤ ∑ p ∈ sideShapeBucket Finset.univ
        (fun p ↦ selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
          weight p := by
    apply Finset.sum_nonneg
    intro p _hp
    exact hweightNonneg p
  refine ⟨label, hoccupied, ?_, ha, hab, hb, hplank⟩
  calc
    (∑ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}, weight p) ≤
        (occupiedWeightBuckets
          (Finset.univ : Finset
            {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
          (fun p ↦ sideShapeLabel
            (selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p))).card *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p ↦ selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
            weight p) := hretained
    _ ≤ selectedParentSideBucketLoss rho r *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p ↦ selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
            weight p) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hbucketNonneg

/-! ## Cancellation of the common scalar scale in the logarithmic loss -/

/-- A cubic ceil-log loss written only in terms of the ratio between the
upper and lower side scales. -/
def threeSideDyadicRatioLoss (ratio : Real) : Nat :=
  ((dyadicCeilBucket ratio + 1).toNat) ^ 3

/-- The interval-form cubic loss is bounded by the ratio-form loss.  This is
the elementary ceiling subadditivity that removes every common scalar
factor from a dyadic bucket count. -/
theorem threeSideDyadicLoss_le_ratioLoss
    {lower upper : Real} (hlower : 0 < lower) (hupper : 0 < upper) :
    threeSideDyadicLoss lower upper ≤
      threeSideDyadicRatioLoss (upper / lower) := by
  have hlog :
      Real.logb 2 upper =
        Real.logb 2 lower + Real.logb 2 (upper / lower) := by
    rw [Real.logb_div hupper.ne' hlower.ne']
    ring
  have hceil := Int.ceil_add_le
    (Real.logb 2 lower) (Real.logb 2 (upper / lower))
  have hspanInt :
      dyadicCeilBucket upper + 1 - dyadicCeilBucket lower ≤
        dyadicCeilBucket (upper / lower) + 1 := by
    unfold dyadicCeilBucket
    rw [hlog]
    omega
  have hspanNat := Int.toNat_le_toNat hspanInt
  exact Nat.pow_le_pow_left hspanNat 3

/-- The final paper-scale loss: visibly cubic in one base-two logarithm of
`5971968/rho`, and independent of the auxiliary common contraction `r`. -/
def selectedParentLogarithmicSideBucketLoss (rho : NNReal) : Nat :=
  threeSideDyadicRatioLoss (5971968 / (rho : Real))

/-- The literal `[r*rho/3456,1728*r]` loss is bounded by the scale-free
`O(log(1/rho)^3)` expression; the common factor `r` cancels exactly. -/
theorem selectedParentSideBucketLoss_le_logarithmic
    (hrho : 0 < rho) (r : NNReal) (hr : 0 < r) :
    selectedParentSideBucketLoss rho r ≤
      selectedParentLogarithmicSideBucketLoss rho := by
  have hlower : (0 : Real) < (selectedParentSideFloor rho r : Real) := by
    exact_mod_cast selectedParentSideFloor_pos hrho hr
  have hupper : (0 : Real) < ((1728 * r : NNReal) : Real) := by
    positivity
  have hratio :
      (((1728 * r : NNReal) : Real) /
        (selectedParentSideFloor rho r : Real)) =
          5971968 / (rho : Real) := by
    unfold selectedParentSideFloor
    norm_num [NNReal.coe_div, NNReal.coe_mul]
    field_simp [show (r : Real) ≠ 0 by exact_mod_cast hr.ne',
      show (rho : Real) ≠ 0 by exact_mod_cast hrho.ne']
    norm_num
  unfold selectedParentSideBucketLoss
    selectedParentLogarithmicSideBucketLoss
  rw [← hratio]
  exact threeSideDyadicLoss_le_ratioLoss hlower hupper

/-- Scale-free occupied-label bound in the paper form
`O(log(1/rho)^3)`. -/
theorem selectedParent_occupiedSideShapeLabels_card_le_logarithmic
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let side : parent → Fin 3 → NNReal := fun p ↦
      selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p
    (occupiedWeightBuckets (Finset.univ : Finset parent)
      (fun p ↦ sideShapeLabel (side p))).card ≤
        selectedParentLogarithmicSideBucketLoss rho := by
  dsimp only
  exact (selectedParent_occupiedSideShapeLabels_card_le
    hfineContained S hrho hrhoOne P k r hr).trans
      (selectedParentSideBucketLoss_le_logarithmic hrho r hr)

/-- Final actual Family8 plank bucket with a scale-independent explicit
cubic logarithmic loss. -/
theorem exists_selectedParentActualIsPlankBucket_logarithmicLoss
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (weight :
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} → Real)
    (hweightNonneg : ∀ p, 0 ≤ weight p) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let side : parent → Fin 3 → NNReal := fun p ↦
      selectedParentLongRelabeledSide e S
        (blockAt S.activeCoarseFamily P k).fiber hrho p
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p ↦ sideShapeLabel (side p)) ∧
      (∑ p : parent, weight p) ≤
        selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ side label, weight p) ∧
      0 < bucketShortA label ∧
      bucketShortA label ≤ bucketShortB label ∧
      bucketShortB label ≤ 1 ∧
      ∀ p, p ∈ sideShapeBucket Finset.univ side label →
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S
            (blockAt S.activeCoarseFamily P k).fiber p) := by
  dsimp only
  have hbucket := exists_selectedParentActualIsPlankBucket_explicitLoss
    hfineContained S hrho hrhoOne P k r hr weight hweightNonneg
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  have hloss := selectedParentSideBucketLoss_le_logarithmic hrho r hr
  have hbucketNonneg :
      0 ≤ ∑ p ∈ sideShapeBucket Finset.univ
        (fun p ↦ selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
          weight p := by
    apply Finset.sum_nonneg
    intro p _hp
    exact hweightNonneg p
  refine ⟨label, hoccupied, ?_, ha, hab, hb, hplank⟩
  calc
    (∑ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}, weight p) ≤
        selectedParentSideBucketLoss rho r *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p ↦ selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
            weight p) := hretained
    _ ≤ selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p ↦ selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
            weight p) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hloss) hbucketNonneg


/-- The paper-facing specialization: admissibility supplies the ambient
unit-ball support used to quantify the John inverse, so no geometric floor
or operator estimate is exposed as an additional premise. -/
theorem exists_selectedParentActualIsPlankBucket_logarithmicLoss_of_admissible
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (weight :
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} → Real)
    (hweightNonneg : ∀ p, 0 ≤ weight p) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let side : parent → Fin 3 → NNReal := fun p ↦
      selectedParentLongRelabeledSide e S
        (blockAt S.activeCoarseFamily P k).fiber hrho p
    ∃ label : Fin 3 → Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p ↦ sideShapeLabel (side p)) ∧
      (∑ p : parent, weight p) ≤
        selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ side label, weight p) ∧
      0 < bucketShortA label ∧
      bucketShortA label ≤ bucketShortB label ∧
      bucketShortB label ≤ 1 ∧
      ∀ p, p ∈ sideShapeBucket Finset.univ side label →
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S
            (blockAt S.activeCoarseFamily P k).fiber p) := by
  exact exists_selectedParentActualIsPlankBucket_logarithmicLoss
    hD.contained_in_unit_ball S hrho hrhoOne P k r hr weight hweightNonneg

#print axioms PositiveJohnFrame.symm_dist_le_three_mul_of_side_le
#print axioms selectedParentGreedyBlockJohnSide_le_2304
#print axioms contractedJohnAffineEquiv_symm_dist_le
#print axioms selectedParentContracted_closedBall_subset
#print axioms selectedParentContractedLongRelabeledSide_floor
#print axioms card_occupied_sideShapeLabel_le
#print axioms selectedParent_occupiedSideShapeLabels_card_le_logarithmic
#print axioms exists_selectedParentActualIsPlankBucket_logarithmicLoss
#print axioms exists_selectedParentActualIsPlankBucket_logarithmicLoss_of_admissible
end
end Family8SelectedParentJohnPlankQuantitativeLossV9
