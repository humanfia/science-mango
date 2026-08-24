import FamilyStickyCinematicL32ActualSameScaleCoverFullCoefficientCapV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32ActualSameScaleCoverParallelLossCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualSameScaleCoverFiberCapV1
open FamilyStickyCinematicL32ActualSameScaleCoverFullCoefficientCapV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u} [DecidableEq iota]
  {fine : UniformTubeFamily delta iota} {active : Finset iota}
  (C : @TubeScaleCover delta delta iota _ fine active)

/-!
# Full coefficient cap from the actual scale-cover parallel loss

The primitive extremal `scale_covers` field controls the cardinality of
every literal parallel cluster, not the total number of cover parents.  This
module keeps that faithful quantity through the same-radius rigidity and
finite `13^3` coefficient cover.
-/

theorem activeNearCoefficientIndices_card_le_parallelLoss_of_activeCenter
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} {parallelLoss : Nat}
    (hcluster : forall U : Tube delta,
      (C.parallelCluster U).card ≤ parallelLoss)
    (j : iota) (hj : j ∈ active)
    (hnear : forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j) scale ->
        EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j)) :
    (activeNearCoefficientIndices fine active (fine.tubes j) scale).card ≤
      parallelLoss := by
  have hfibre := activeNearCoefficientIndices_card_le_parent_card
    C hdelta hpair (fine.tubes j) scale
  have hparents :=
    actualNearCoefficientCoverParents_subset_parallelCluster_of_activeCenter
      C j hj hnear
  exact hfibre.trans <|
    (Finset.card_le_card hparents).trans
      (hcluster (C.tubes (C.parent j)))

theorem activeNearCoefficientIndices_card_le_coverLoss_mul_parallelLoss
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {parallelLoss : Nat}
    (hcluster : forall U : Tube delta,
      (C.parallelCluster U).card ≤ parallelLoss)
    (hhalfParallel : forall j, j ∈ active -> forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j)
        ((delta : Real) / 2) ->
      EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j))
    (center : Tube delta) :
    (activeNearCoefficientIndices fine active center (delta : Real)).card ≤
      actualHalfScaleCoefficientCoverLoss * parallelLoss := by
  apply activeNearCoefficientIndices_card_le_full_of_half
    fine active hdelta
  intro j hj
  exact activeNearCoefficientIndices_card_le_parallelLoss_of_activeCenter
    C hdelta hpair hcluster j hj (hhalfParallel j hj)

theorem activeNearCoefficientIndices_card_le_multiplicity_of_parallelLoss
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {parallelLoss multiplicity : Nat}
    (hcluster : forall U : Tube delta,
      (C.parallelCluster U).card ≤ parallelLoss)
    (hhalfParallel : forall j, j ∈ active -> forall i,
      i ∈ activeNearCoefficientIndices fine active (fine.tubes j)
        ((delta : Real) / 2) ->
      EssentiallyParallelAtScale (fine.tubes i) (fine.tubes j))
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤ multiplicity)
    (center : Tube delta) :
    (activeNearCoefficientIndices fine active center (delta : Real)).card ≤
      multiplicity :=
  (activeNearCoefficientIndices_card_le_coverLoss_mul_parallelLoss
    C hdelta hpair hcluster hhalfParallel center).trans hloss

#print axioms activeNearCoefficientIndices_card_le_parallelLoss_of_activeCenter
#print axioms activeNearCoefficientIndices_card_le_coverLoss_mul_parallelLoss
#print axioms activeNearCoefficientIndices_card_le_multiplicity_of_parallelLoss

end

end FamilyStickyCinematicL32ActualSameScaleCoverParallelLossCapV1
