import Family8Grounding.Family8GreedyWinnerNormalizedPlankBucketV1
import Mathlib.Tactic

/-!
# Quantitative bounds for the common greedy-winner normalization scalar

A complete unit-axis tube inside a greedy winner and the outer John box force
one John side to be strictly larger than `1/2`.  Longest-axis relabeling puts
that strict lower bound in coordinate `2`.  For a selected dyadic side bucket,
the common long endpoint is therefore at least `1`; the automatic unit-ball
ceiling and the integer ceil-log structure bound it by `1024`.

Consequently the common scalar used by the normalized winner family lies in
`[1/1024,1]`.  These are bounds for the shared normalized coordinate system;
they do not pull a normalized tube cover back to the original fine family.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8GreedyWinnerNormalizationScalarBoundsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8GreedyWinnerNormalizedPlankBucketV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- A complete unit-axis tube inside the outer box of a box-dimensions
certificate forces one side to be strictly larger than `1/2`.  The strict
form follows from three-coordinate Parseval: three coordinates bounded by
`1/2` would have squared sum at most `3/4`, not `1`. -/
theorem exists_half_lt_boxSide_of_unitTube_subset
    {rho C : NNReal} (T : Tube rho)
    {K : ConvexBody Space} {side : Fin 3 -> NNReal}
    (cert : BoxDimensionsCertificate C side K)
    (hT : T.carrier ⊆ (K : Set Space)) :
    exists i : Fin 3, (1 / 2 : NNReal) < side i := by
  let B := cert.box
  have hbaseTube : T.axis.base ∈ T.carrier :=
    T.axis_subset_carrier T.axis.base_mem_carrier
  have hendTube : T.axis.endpoint ∈ T.carrier :=
    T.axis_subset_carrier T.axis.endpoint_mem_carrier
  have hbase : T.axis.base ∈ B.carrier :=
    cert.outer_le (hT hbaseTube)
  have hend : T.axis.endpoint ∈ B.carrier :=
    cert.outer_le (hT hendTube)
  have hcoord (i : Fin 3) :
      |inner Real (B.frame i) T.axis.direction| <= (side i : Real) := by
    have hb := B.centeredCoordinate_abs_le_halfSide hbase i
    have he := B.centeredCoordinate_abs_le_halfSide hend i
    rw [congrFun cert.side_eq i] at hb he
    change
      |inner Real (B.frame i) T.axis.base -
        inner Real (B.frame i) B.center| <= (side i : Real) / 2 at hb
    change
      |inner Real (B.frame i) T.axis.endpoint -
        inner Real (B.frame i) B.center| <= (side i : Real) / 2 at he
    have htriangle :
        |inner Real (B.frame i) T.axis.endpoint -
            inner Real (B.frame i) T.axis.base| <=
          |inner Real (B.frame i) T.axis.endpoint -
              inner Real (B.frame i) B.center| +
            |inner Real (B.frame i) T.axis.base -
              inner Real (B.frame i) B.center| := by
      calc
        |inner Real (B.frame i) T.axis.endpoint -
            inner Real (B.frame i) T.axis.base| <=
          |inner Real (B.frame i) T.axis.endpoint -
              inner Real (B.frame i) B.center| +
            |inner Real (B.frame i) B.center -
              inner Real (B.frame i) T.axis.base| := abs_sub_le _ _ _
        _ = |inner Real (B.frame i) T.axis.endpoint -
              inner Real (B.frame i) B.center| +
            |inner Real (B.frame i) T.axis.base -
              inner Real (B.frame i) B.center| := by
          rw [abs_sub_comm
            (inner Real (B.frame i) B.center)
            (inner Real (B.frame i) T.axis.base)]
    calc
      |inner Real (B.frame i) T.axis.direction| =
          |inner Real (B.frame i) T.axis.endpoint -
            inner Real (B.frame i) T.axis.base| := by
        simp only [UnitSegment.endpoint, inner_add_right]
        ring
      _ <= |inner Real (B.frame i) T.axis.endpoint -
              inner Real (B.frame i) B.center| +
            |inner Real (B.frame i) T.axis.base -
              inner Real (B.frame i) B.center| := htriangle
      _ <= (side i : Real) / 2 + (side i : Real) / 2 :=
        add_le_add he hb
      _ = (side i : Real) := by ring
  by_contra hnone
  rw [not_exists] at hnone
  have hsmall (i : Fin 3) :
      |inner Real (B.frame i) T.axis.direction| <= (1 / 2 : Real) := by
    exact (hcoord i).trans (by exact_mod_cast le_of_not_gt (hnone i))
  have h0 := abs_le.mp (hsmall 0)
  have h1 := abs_le.mp (hsmall 1)
  have h2 := abs_le.mp (hsmall 2)
  have hparseval := B.frame.sum_sq_inner_right T.axis.direction
  rw [Fin.sum_univ_three, T.axis.norm_direction] at hparseval
  norm_num at h0 h1 h2
  nlinarith [sq_nonneg (inner Real (B.frame 0) T.axis.direction),
    sq_nonneg (inner Real (B.frame 1) T.axis.direction),
    sq_nonneg (inner Real (B.frame 2) T.axis.direction)]

/-- The automatic longest-axis relabeling puts the strict Parseval lower
bound in the winner's coordinate `2`. -/
theorem half_lt_winnerLongSide_two
    (hdelta : 0 < delta)
    (k : Fin (blocks fine.bodyFamily P).length) :
    (1 / 2 : NNReal) < winnerLongSide P hdelta k 2 := by
  obtain ⟨i, hi⟩ := exists_half_lt_boxSide_of_unitTube_subset
    (fine.tubes (winnerWitness P k))
    (winnerJohnCertificate P hdelta k)
    (winnerWitness_tube_subset P k)
  have hle : winnerJohnSide P hdelta k i <=
      winnerLongSide P hdelta k 2 := by
    unfold winnerLongSide
    rw [relabeledSide_apply]
    simp only [longAxisPermutation, Equiv.symm_swap, Equiv.swap_apply_left]
    exact side_le_longestSideIndex (winnerJohnSide P hdelta k) i
  exact hi.trans_le hle

/-- The common long dyadic endpoint of any occupied winner bucket is at
least one.  The strict `1/2` input is essential here. -/
theorem one_le_sideShapeUpper_two_of_mem_winnerSideBucket
    (hdelta : 0 < delta) (label : Fin 3 -> Int)
    (k : Fin (blocks fine.bodyFamily P).length)
    (hk : k ∈ sideShapeBucket Finset.univ
      (winnerLongSide P hdelta) label) :
    1 <= sideShapeUpper label 2 := by
  have hkLabel := (mem_sideShapeBucket_iff Finset.univ
    (winnerLongSide P hdelta) label k).1 hk |>.2
  have hsidePos : (0 : Real) < (winnerLongSide P hdelta k 2 : Real) := by
    exact_mod_cast winnerLongSide_pos P hdelta k 2
  have hhalfReal : (1 / 2 : Real) <
      (winnerLongSide P hdelta k 2 : Real) := by
    exact_mod_cast half_lt_winnerLongSide_two P hdelta k
  have hlogLower : (-1 : Real) <
      Real.logb 2 (winnerLongSide P hdelta k 2 : Real) := by
    apply (Real.lt_logb_iff_rpow_lt (b := (2 : Real))
      (by norm_num) hsidePos).2
    norm_num [Real.rpow_neg_one]
    exact hhalfReal
  have hbucketNonneg : 0 <= dyadicCeilBucket
      (winnerLongSide P hdelta k 2 : Real) := by
    unfold dyadicCeilBucket
    exact Int.ceil_nonneg_of_neg_one_lt hlogLower
  have hkLabel2 := congrFun hkLabel 2
  change dyadicCeilBucket (winnerLongSide P hdelta k 2 : Real) =
    label 2 at hkLabel2
  have hlabelNonneg : (0 : Int) <= label 2 := by
    rw [← hkLabel2]
    exact hbucketNonneg
  have hreal : (1 : Real) <= dyadicCeilUpper (label 2) := by
    unfold dyadicCeilUpper
    have hexp : (0 : Real) <= ((label 2 : Int) : Real) := by
      exact_mod_cast hlabelNonneg
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2)
        hexp)
  exact_mod_cast hreal

/-- The unit-ball ceiling `winnerLongSide <= 576`, together with the exact
integer ceil-log endpoint, improves the naive factor-two bound `1152` to the
next lower dyadic endpoint `1024`. -/
theorem sideShapeUpper_two_le_1024_of_mem_winnerSideBucket
    (hdelta : 0 < delta)
    (hfineContained : forall i, i ∈ active ->
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (label : Fin 3 -> Int)
    (k : Fin (blocks fine.bodyFamily P).length)
    (hk : k ∈ sideShapeBucket Finset.univ
      (winnerLongSide P hdelta) label) :
    sideShapeUpper label 2 <= 1024 := by
  have hkLabel := (mem_sideShapeBucket_iff Finset.univ
    (winnerLongSide P hdelta) label k).1 hk |>.2
  have hkLabel2 := congrFun hkLabel 2
  change dyadicCeilBucket (winnerLongSide P hdelta k 2 : Real) =
    label 2 at hkLabel2
  have hsidePos : (0 : Real) < (winnerLongSide P hdelta k 2 : Real) := by
    exact_mod_cast winnerLongSide_pos P hdelta k 2
  have hsideUpper : (winnerLongSide P hdelta k 2 : Real) <= 1024 := by
    exact_mod_cast (winnerLongSide_le_576 P hdelta hfineContained k 2).trans
      (by norm_num : (576 : NNReal) <= 1024)
  have hbucket1024 : dyadicCeilBucket (1024 : Real) = 10 := by
    rw [show (1024 : Real) = 2 ^ 10 by norm_num]
    unfold dyadicCeilBucket
    rw [Real.logb_pow]
    rw [Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hmono := dyadicCeilBucket_mono hsidePos hsideUpper
  have hlabelLe : label 2 <= (10 : Int) := by
    rw [← hkLabel2]
    simpa only [hbucket1024] using hmono
  have hreal : dyadicCeilUpper (label 2) <= (1024 : Real) := by
    unfold dyadicCeilUpper
    have hexp : ((label 2 : Int) : Real) <= (10 : Real) := by
      exact_mod_cast hlabelLe
    calc
      (2 : Real) ^ ((label 2 : Int) : Real) <=
          (2 : Real) ^ (10 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1024 := by norm_num
  exact_mod_cast hreal

/-- The common normalization scalar of an occupied winner bucket lies in the
explicit compact interval `[1/1024,1]`. -/
theorem winnerBucket_normalizationScalar_bounds
    (hdelta : 0 < delta)
    (hfineContained : forall i, i ∈ active ->
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (label : Fin 3 -> Int)
    (k : Fin (blocks fine.bodyFamily P).length)
    (hk : k ∈ sideShapeBucket Finset.univ
      (winnerLongSide P hdelta) label) :
    (1024 : NNReal)⁻¹ <= (sideShapeUpper label 2)⁻¹ ∧
      (sideShapeUpper label 2)⁻¹ <= 1 := by
  have huPos : 0 < sideShapeUpper label 2 := sideShapeUpper_pos label 2
  have hlower := one_le_sideShapeUpper_two_of_mem_winnerSideBucket
    P hdelta label k hk
  have hupper := sideShapeUpper_two_le_1024_of_mem_winnerSideBucket
    P hdelta hfineContained label k hk
  exact ⟨(inv_le_inv₀ (by norm_num) huPos).2 hupper,
    (inv_le_one₀ huPos).2 hlower⟩

/-- The same scalar interval exposed directly on the normalized-bucket
witness constructed in the preceding module. -/
theorem GreedyWinnerNormalizedPlankBucket.normalizationScalar_bounds
    (hdelta : 0 < delta)
    (W : GreedyWinnerNormalizedPlankBucket P hdelta)
    (hfineContained : forall i, i ∈ active ->
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (k : Fin (blocks fine.bodyFamily P).length) (hk : k ∈ W.selected) :
    (1024 : NNReal)⁻¹ <= (sideShapeUpper W.label 2)⁻¹ ∧
      (sideShapeUpper W.label 2)⁻¹ <= 1 := by
  apply winnerBucket_normalizationScalar_bounds
    P hdelta hfineContained W.label k
  rw [W.selected_eq] at hk
  exact hk

#print axioms exists_half_lt_boxSide_of_unitTube_subset
#print axioms half_lt_winnerLongSide_two
#print axioms one_le_sideShapeUpper_two_of_mem_winnerSideBucket
#print axioms sideShapeUpper_two_le_1024_of_mem_winnerSideBucket
#print axioms winnerBucket_normalizationScalar_bounds
#print axioms GreedyWinnerNormalizedPlankBucket.normalizationScalar_bounds

end
end Family8GreedyWinnerNormalizationScalarBoundsV1
