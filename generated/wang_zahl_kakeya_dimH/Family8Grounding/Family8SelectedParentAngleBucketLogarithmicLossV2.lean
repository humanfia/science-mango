import Family8Grounding.Family8SelectedParentExactAssemblyCordobaExpandedV6
import Mathlib.Tactic

/-!
# Logarithmic bound for the actual selected-parent angle buckets, V2

Canonical successor to the mechanically failed V1.  An occupied side label
contains an actual selected parent.  The proved selected-parent side floor
and upper bound therefore control the ratio of its two normalized short
dyadic endpoints.  No angle or container conclusion is assumed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentAngleBucketLogarithmicLossV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A thresholded angle count whose aspect ratio is at most `R` is bounded
by twice the cubic dyadic logarithmic loss at `R`. -/
theorem certifiedPlankThresholdedAngleBucketLoss_le_two_mul_ratioLoss
    {a b : NNReal} (ha : 0 < a) (hab : a <= b)
    {R : Real} (hratio : (((b / a : NNReal) : Real)) <= R) :
    certifiedPlankThresholdedAngleBucketLoss a b <=
      2 * threeSideDyadicRatioLoss R := by
  have hbaOne : (1 : Real) <= (((b / a : NNReal) : Real)) := by
    rw [NNReal.coe_div]
    apply (le_div_iff₀
      (show (0 : Real) < (a : Real) by exact_mod_cast ha)).2
    simpa only [one_mul] using (show (a : Real) <= (b : Real) by
      exact_mod_cast hab)
  have hROne : (1 : Real) <= R := hbaOne.trans hratio
  have hbaPos : (0 : Real) < (((b / a : NNReal) : Real)) :=
    lt_of_lt_of_le (by norm_num) hbaOne
  have hceil :
      dyadicCeilBucket (((b / a : NNReal) : Real)) <=
        dyadicCeilBucket R :=
    dyadicCeilBucket_mono hbaPos hratio
  have hbucketOne : dyadicCeilBucket (1 : Real) = 0 := by
    norm_num [dyadicCeilBucket, Real.logb]
  have hceilRNonneg : 0 <= dyadicCeilBucket R := by
    have hmono := dyadicCeilBucket_mono
      (r := (1 : Real)) (s := R) (by norm_num) hROne
    simpa only [hbucketOne] using hmono
  let n : Nat := (dyadicCeilBucket R + 1).toNat
  have hn : 1 <= n := by
    dsimp only [n]
    omega
  have hspan :
      (dyadicCeilBucket (((b / a : NNReal) : Real)) + 1 -
          dyadicCeilBucket (1 : Real)).toNat <= n := by
    rw [hbucketOne, sub_zero]
    dsimp only [n]
    apply Int.toNat_le_toNat
    omega
  have hnCube : n <= n ^ 3 := by
    calc
      n = n * 1 := by simp
      _ <= n * (n * n) := by
        exact Nat.mul_le_mul_left n (Nat.mul_le_mul hn hn)
      _ = n ^ 3 := by ring
  unfold certifiedPlankThresholdedAngleBucketLoss
    threeSideDyadicRatioLoss
  calc
    (dyadicCeilBucket (((b / a : NNReal) : Real)) + 1 -
        dyadicCeilBucket (1 : Real)).toNat + 1 <= n + 1 :=
      Nat.add_le_add_right hspan 1
    _ <= 2 * n := by omega
    _ <= 2 * (n ^ 3) := Nat.mul_le_mul_left 2 hnCube

/-- For an occupied actual selected-parent side label, the two normalized
short endpoints have ratio at most `11943936 / rho`.  The common John
contraction `r` cancels exactly. -/
theorem bucketShortB_div_bucketShortA_le_selectedParentRatio
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p))) :
    (((bucketShortB label / bucketShortA label : NNReal) : Real)) <=
      11943936 / (rho : Real) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side : {p // p ∈ B} -> Fin 3 -> NNReal := fun p =>
    selectedParentLongRelabeledSide e S B hrho p
  rcases mem_occupiedWeightBuckets_iff.mp hoccupied with
    ⟨p, _hp, hpLabel⟩
  have hpos : forall i, 0 < side p i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho p i
  have hband0 := sideShapeUpper_half_lt_and_le hpos (0 : Fin 3)
  have hband1 := sideShapeUpper_half_lt_and_le hpos (1 : Fin 3)
  change sideShapeLabel (side p) = label at hpLabel
  rw [hpLabel] at hband0 hband1
  have hfloor0 : selectedParentSideFloor rho r <= side p 0 := by
    exact selectedParentContractedLongRelabeledSide_floor
      hfineContained S hrho hrhoOne P k r hr p 0
  have hfloor1 : selectedParentSideFloor rho r <= side p 1 := by
    exact selectedParentContractedLongRelabeledSide_floor
      hfineContained S hrho hrhoOne P k r hr p 1
  have hside0Upper : side p 0 <= 1728 * r := by
    exact selectedParentContractedLongRelabeledSide_le
      S hrho P k r hr p 0
  have hside1Upper : side p 1 <= 1728 * r := by
    exact selectedParentContractedLongRelabeledSide_le
      S hrho P k r hr p 1
  have hU0Lower : selectedParentSideFloor rho r <=
      sideShapeUpper label 0 := hfloor0.trans hband0.2
  have hU1Lower : selectedParentSideFloor rho r <=
      sideShapeUpper label 1 := hfloor1.trans hband1.2
  have hU0Upper : sideShapeUpper label 0 <= 3456 * r := by
    apply le_of_lt
    nlinarith [hband0.1, hside0Upper]
  have hU1Upper : sideShapeUpper label 1 <= 3456 * r := by
    apply le_of_lt
    nlinarith [hband1.1, hside1Upper]
  have hU0Pos : (0 : Real) < (sideShapeUpper label 0 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 0
  have hU1Pos : (0 : Real) < (sideShapeUpper label 1 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 1
  have hU2Pos : (0 : Real) < (sideShapeUpper label 2 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 2
  have hfloorPos : (0 : Real) <
      (selectedParentSideFloor rho r : Real) := by
    exact_mod_cast selectedParentSideFloor_pos hrho hr
  have hU0LowerReal : (selectedParentSideFloor rho r : Real) <=
      (sideShapeUpper label 0 : Real) := by exact_mod_cast hU0Lower
  have hU1LowerReal : (selectedParentSideFloor rho r : Real) <=
      (sideShapeUpper label 1 : Real) := by exact_mod_cast hU1Lower
  have hU0UpperReal : (sideShapeUpper label 0 : Real) <=
      ((3456 * r : NNReal) : Real) := by exact_mod_cast hU0Upper
  have hU1UpperReal : (sideShapeUpper label 1 : Real) <=
      ((3456 * r : NNReal) : Real) := by exact_mod_cast hU1Upper
  have hscale :
      (((3456 * r : NNReal) : Real) /
          (selectedParentSideFloor rho r : Real)) =
        11943936 / (rho : Real) := by
    unfold selectedParentSideFloor
    norm_num [NNReal.coe_div, NNReal.coe_mul]
    field_simp [show (r : Real) ≠ 0 by exact_mod_cast hr.ne',
      show (rho : Real) ≠ 0 by exact_mod_cast hrho.ne']
    ring
  by_cases h01 : sideShapeUpper label 0 <= sideShapeUpper label 1
  · simp only [bucketShortA, bucketShortB, if_pos h01, NNReal.coe_div]
    have hcancel :
        (((sideShapeUpper label 1 : Real) /
            (sideShapeUpper label 2 : Real)) /
          ((sideShapeUpper label 0 : Real) /
            (sideShapeUpper label 2 : Real))) =
          (sideShapeUpper label 1 : Real) /
            (sideShapeUpper label 0 : Real) := by
      field_simp [hU0Pos.ne', hU2Pos.ne']
    rw [hcancel, ← hscale]
    exact div_le_div₀ (by positivity) hU1UpperReal hfloorPos hU0LowerReal
  · simp only [bucketShortA, bucketShortB, if_neg h01, NNReal.coe_div]
    have hcancel :
        (((sideShapeUpper label 0 : Real) /
            (sideShapeUpper label 2 : Real)) /
          ((sideShapeUpper label 1 : Real) /
            (sideShapeUpper label 2 : Real))) =
          (sideShapeUpper label 0 : Real) /
            (sideShapeUpper label 1 : Real) := by
      field_simp [hU1Pos.ne', hU2Pos.ne']
    rw [hcancel, ← hscale]
    exact div_le_div₀ (by positivity) hU0UpperReal hfloorPos hU1LowerReal

/-- Hence the actual thresholded angle-cardinality loss is logarithmic in
the selected-parent scale, independently of the auxiliary contraction. -/
theorem selectedParent_angleBucketLoss_le_logarithmic
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p))) :
    certifiedPlankThresholdedAngleBucketLoss
        (bucketShortA label) (bucketShortB label) <=
      2 * threeSideDyadicRatioLoss (11943936 / (rho : Real)) := by
  apply certifiedPlankThresholdedAngleBucketLoss_le_two_mul_ratioLoss
    (bucketShortA_pos label) (bucketShortA_le_bucketShortB label)
  exact bucketShortB_div_bucketShortA_le_selectedParentRatio
    hfineContained S hrho hrhoOne P k r hr label hoccupied

#print axioms certifiedPlankThresholdedAngleBucketLoss_le_two_mul_ratioLoss
#print axioms bucketShortB_div_bucketShortA_le_selectedParentRatio
#print axioms selectedParent_angleBucketLoss_le_logarithmic

end

end Family8SelectedParentAngleBucketLogarithmicLossV2
