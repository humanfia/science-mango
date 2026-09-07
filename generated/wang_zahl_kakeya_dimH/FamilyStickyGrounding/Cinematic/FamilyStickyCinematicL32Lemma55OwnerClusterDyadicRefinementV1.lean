import FamilyStickyCinematicL32FiniteWeightedBucketV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringTwoScaleV1
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped BigOperators

namespace FamilyStickyCinematicL32Lemma55OwnerClusterDyadicRefinementV1

open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringTwoScaleV1

noncomputable section

universe u

/-!
# The owner-cluster dyadic refinement in PYZ Section 5.3

After the maximal `100`-incomparable coarse pivots have been chosen, the
fine rectangles are partitioned into owner fibres.  This file performs the
next, purely finite, pigeonhole step: it retains one dyadic class of nonempty
owner fibres, with a common cardinality scale `M`, and records the exact
logarithmic loss.

This is deliberately only the cluster-cardinality refinement.  Bounding `M`
in the paper additionally uses disjoint fine shadings, their common lower
measure, and containment in an enlarged coarse rectangle.
-/

/-- Cardinality of the raw owner fibre over a pivot. -/
def ownerClusterCard {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha) (owner : alpha -> alpha) (pivot : alpha) : Nat :=
  (vertices.filter fun a => owner a = pivot).card

/-- Pivots whose owner fibre is nonempty.  Empty fibres carry no cardinality
and are discarded before dyadic pigeonholing. -/
def nonemptyOwnerPivots {alpha : Type u} [DecidableEq alpha]
    (vertices pivots : Finset alpha) (owner : alpha -> alpha) : Finset alpha :=
  pivots.filter fun b => 0 < ownerClusterCard vertices owner b

/-- Base-two dyadic level of one owner fibre. -/
def ownerClusterDyadicLevel {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha) (owner : alpha -> alpha) (pivot : alpha) : Nat :=
  Nat.log 2 (ownerClusterCard vertices owner pivot)

/-- Pivots in a fixed occupied dyadic owner-cardinality class. -/
def ownerClusterDyadicPivots {alpha : Type u} [DecidableEq alpha]
    (vertices pivots : Finset alpha) (owner : alpha -> alpha)
    (level : Nat) : Finset alpha :=
  (nonemptyOwnerPivots vertices pivots owner).filter fun b =>
    ownerClusterDyadicLevel vertices owner b = level

/-- Raw vertices retained above a selected collection of owner pivots. -/
def ownerClusterUnion {alpha : Type u} [DecidableEq alpha]
    (vertices selectedPivots : Finset alpha) (owner : alpha -> alpha) :
    Finset alpha :=
  vertices.filter fun a => owner a ∈ selectedPivots

/-- The explicit number of possible dyadic cardinality levels. -/
def ownerClusterBucketLoss {alpha : Type u}
    (vertices : Finset alpha) : Nat :=
  Nat.log 2 vertices.card + 1

/-- Output of the owner-cardinality pigeonhole step.  Its selected fibres
have sizes in `[2^level, 2 * 2^level)`, their union is an exact disjoint fibre
sum, and it retains at least a `1 / ownerClusterBucketLoss` fraction in the
denominator-free cardinality sense. -/
structure OwnerClusterDyadicRefinement
    {alpha : Type u} [DecidableEq alpha]
    (vertices pivots : Finset alpha) (owner : alpha -> alpha) where
  level : Nat
  selectedPivots : Finset alpha
  selectedPivots_eq :
    selectedPivots = ownerClusterDyadicPivots vertices pivots owner level
  selectedPivots_nonempty : selectedPivots.Nonempty
  selectedPivots_subset : selectedPivots ⊆ pivots
  level_lt_bucketLoss : level < ownerClusterBucketLoss vertices
  occupied_bucket_card_le_loss :
    (occupiedWeightBuckets (nonemptyOwnerPivots vertices pivots owner)
      (ownerClusterDyadicLevel vertices owner)).card <=
        ownerClusterBucketLoss vertices
  clusterCard_bounds : forall b, b ∈ selectedPivots ->
    2 ^ level <= ownerClusterCard vertices owner b ∧
      ownerClusterCard vertices owner b < 2 * 2 ^ level
  retained_card_eq_cluster_sum :
    (ownerClusterUnion vertices selectedPivots owner).card =
      ∑ b ∈ selectedPivots, ownerClusterCard vertices owner b
  full_card_le_loss_mul_retained_card :
    vertices.card <= ownerClusterBucketLoss vertices *
      (ownerClusterUnion vertices selectedPivots owner).card
  selected_card_mul_scale_le_retained_card :
    selectedPivots.card * 2 ^ level <=
      (ownerClusterUnion vertices selectedPivots owner).card
  retained_card_le_selected_card_mul_twice_scale :
    (ownerClusterUnion vertices selectedPivots owner).card <=
      selectedPivots.card * (2 * 2 ^ level)
  retained_nonempty :
    (ownerClusterUnion vertices selectedPivots owner).Nonempty

/-- Dyadic pigeonholing of any exact finite owner partition. -/
theorem exists_ownerCluster_dyadic_refinement
    {alpha : Type u} [DecidableEq alpha]
    (vertices pivots : Finset alpha) (owner : alpha -> alpha)
    (hvertices : vertices.Nonempty)
    (hcardPartition : vertices.card =
      ∑ b ∈ pivots, ownerClusterCard vertices owner b) :
    Nonempty (OwnerClusterDyadicRefinement vertices pivots owner) := by
  classical
  let positivePivots := nonemptyOwnerPivots vertices pivots owner
  let levelOf := ownerClusterDyadicLevel vertices owner
  let clusterWeight : alpha -> Real := fun b =>
    ownerClusterCard vertices owner b
  have hsumPositive :
      (∑ b ∈ positivePivots, ownerClusterCard vertices owner b) =
        vertices.card := by
    rw [hcardPartition]
    apply Finset.sum_subset
    · intro b hb
      exact (Finset.mem_filter.mp hb).1
    · intro b hbPivots hbNotPositive
      have hnot : ¬ 0 < ownerClusterCard vertices owner b := by
        intro hpositive
        exact hbNotPositive (Finset.mem_filter.mpr ⟨hbPivots, hpositive⟩)
      exact Nat.eq_zero_of_not_pos hnot
  have hpositivePivots : positivePivots.Nonempty := by
    have hsumPos :
        0 < ∑ b ∈ pivots, ownerClusterCard vertices owner b := by
      rw [← hcardPartition]
      exact Finset.card_pos.mpr hvertices
    obtain ⟨b, hb, hcard⟩ := Finset.sum_pos_iff.mp hsumPos
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, hcard⟩⟩
  obtain ⟨level, hlevelOccupied, hbucket⟩ :=
    exists_totalWeight_le_card_mul_bucketWeight
      (items := positivePivots) (bucket := levelOf)
        clusterWeight hpositivePivots
  let selectedPivots := ownerClusterDyadicPivots vertices pivots owner level
  rcases mem_occupiedWeightBuckets_iff.mp hlevelOccupied with
    ⟨witness, hwitnessPositive, hwitnessLevel⟩
  have hselectedNonempty : selectedPivots.Nonempty := by
    refine ⟨witness, ?_⟩
    exact Finset.mem_filter.mpr ⟨hwitnessPositive, hwitnessLevel⟩
  have hwitnessSelected : witness ∈ selectedPivots :=
    Finset.mem_filter.mpr ⟨hwitnessPositive, hwitnessLevel⟩
  have hselectedSubset : selectedPivots ⊆ pivots := by
    intro b hb
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  have hlabelsSubset :
      occupiedWeightBuckets positivePivots levelOf ⊆
        Finset.range (ownerClusterBucketLoss vertices) := by
    intro j hj
    rcases mem_occupiedWeightBuckets_iff.mp hj with ⟨b, hb, rfl⟩
    have hcardLe : ownerClusterCard vertices owner b <= vertices.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hlogLe := Nat.log_mono_right (b := 2) hcardLe
    exact Finset.mem_range.mpr (by
      simpa only [levelOf, ownerClusterDyadicLevel,
        ownerClusterBucketLoss] using Nat.lt_succ_of_le hlogLe)
  have hlabelCard :
      (occupiedWeightBuckets positivePivots levelOf).card <=
        ownerClusterBucketLoss vertices := by
    simpa only [Finset.card_range] using Finset.card_le_card hlabelsSubset
  have hlevelLt : level < ownerClusterBucketLoss vertices := by
    have := hlabelsSubset hlevelOccupied
    exact Finset.mem_range.mp this
  have hbounds : forall b, b ∈ selectedPivots ->
      2 ^ level <= ownerClusterCard vertices owner b ∧
        ownerClusterCard vertices owner b < 2 * 2 ^ level := by
    intro b hb
    have hbData := Finset.mem_filter.mp hb
    have hbPositive := (Finset.mem_filter.mp hbData.1).2
    have hbLevel : levelOf b = level := hbData.2
    constructor
    · rw [← hbLevel]
      exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hbPositive)
    · have hupper := Nat.lt_pow_succ_log_self
          (by norm_num : 1 < 2) (ownerClusterCard vertices owner b)
      rw [show Nat.log 2 (ownerClusterCard vertices owner b) = level by
        simpa only [levelOf, ownerClusterDyadicLevel] using hbLevel] at hupper
      simpa only [Nat.succ_eq_add_one, pow_succ, Nat.mul_comm] using hupper
  have hretainedCard :
      (ownerClusterUnion vertices selectedPivots owner).card =
        ∑ b ∈ selectedPivots, ownerClusterCard vertices owner b := by
    have hmaps : (ownerClusterUnion vertices selectedPivots owner : Set alpha).MapsTo
        owner selectedPivots := by
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    calc
      (ownerClusterUnion vertices selectedPivots owner).card =
          ∑ b ∈ selectedPivots,
            ((ownerClusterUnion vertices selectedPivots owner).filter
              fun a => owner a = b).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      _ = ∑ b ∈ selectedPivots, ownerClusterCard vertices owner b := by
        apply Finset.sum_congr rfl
        intro b hb
        congr 1
        ext a
        simp only [ownerClusterUnion, Finset.mem_filter]
        constructor
        · rintro ⟨⟨ha, _⟩, hab⟩
          exact ⟨ha, hab⟩
        · rintro ⟨ha, hab⟩
          exact ⟨⟨ha, by simpa only [hab] using hb⟩, hab⟩
  have hbucket' :
      (vertices.card : Real) <=
        ((occupiedWeightBuckets positivePivots levelOf).card : Real) *
          ∑ b ∈ selectedPivots,
            (ownerClusterCard vertices owner b : Real) := by
    have hsumPositiveReal :
        (∑ b ∈ positivePivots,
          (ownerClusterCard vertices owner b : Real)) =
            (vertices.card : Real) := by
      exact_mod_cast hsumPositive
    calc
      (vertices.card : Real) =
          ∑ b ∈ positivePivots,
            (ownerClusterCard vertices owner b : Real) :=
        hsumPositiveReal.symm
      _ <= ((occupiedWeightBuckets positivePivots levelOf).card : Real) *
          bucketWeight positivePivots levelOf clusterWeight level := hbucket
      _ = ((occupiedWeightBuckets positivePivots levelOf).card : Real) *
          ∑ b ∈ selectedPivots,
            (ownerClusterCard vertices owner b : Real) := by
        simp only [bucketWeight, selectedPivots,
          ownerClusterDyadicPivots, positivePivots, levelOf,
          clusterWeight]
  have hselectedSumNonneg :
      (0 : Real) <= ∑ b ∈ selectedPivots,
        (ownerClusterCard vertices owner b : Real) := by positivity
  have hlossReal :
      ((occupiedWeightBuckets positivePivots levelOf).card : Real) <=
        (ownerClusterBucketLoss vertices : Real) := by
    exact_mod_cast hlabelCard
  have hfullReal :
      (vertices.card : Real) <=
        (ownerClusterBucketLoss vertices : Real) *
          ∑ b ∈ selectedPivots,
            (ownerClusterCard vertices owner b : Real) :=
    hbucket'.trans (mul_le_mul_of_nonneg_right hlossReal hselectedSumNonneg)
  have hselectedSumCast :
      (∑ b ∈ selectedPivots,
        (ownerClusterCard vertices owner b : Real)) =
          ((∑ b ∈ selectedPivots,
            ownerClusterCard vertices owner b : Nat) : Real) := by
    norm_cast
  rw [hselectedSumCast] at hfullReal
  have hfullNat :
      vertices.card <= ownerClusterBucketLoss vertices *
        ∑ b ∈ selectedPivots, ownerClusterCard vertices owner b := by
    exact_mod_cast hfullReal
  have hlowerSum :
      selectedPivots.card * 2 ^ level <=
        ∑ b ∈ selectedPivots, ownerClusterCard vertices owner b := by
    calc
      selectedPivots.card * 2 ^ level =
          ∑ _b ∈ selectedPivots, 2 ^ level := by simp
      _ <= ∑ b ∈ selectedPivots, ownerClusterCard vertices owner b :=
        Finset.sum_le_sum fun b hb => (hbounds b hb).1
  have hupperSum :
      (∑ b ∈ selectedPivots, ownerClusterCard vertices owner b) <=
        selectedPivots.card * (2 * 2 ^ level) := by
    calc
      (∑ b ∈ selectedPivots, ownerClusterCard vertices owner b) <=
          ∑ _b ∈ selectedPivots, (2 * 2 ^ level) :=
        Finset.sum_le_sum fun b hb => (hbounds b hb).2.le
      _ = selectedPivots.card * (2 * 2 ^ level) := by simp
  have hretainedNonempty :
      (ownerClusterUnion vertices selectedPivots owner).Nonempty := by
    apply Finset.card_pos.mp
    rw [hretainedCard]
    exact Finset.sum_pos_iff.mpr
      ⟨witness, hwitnessSelected,
        (by positivity : 0 < 2 ^ level).trans_le
          (hbounds witness hwitnessSelected).1⟩
  exact ⟨{
    level := level
    selectedPivots := selectedPivots
    selectedPivots_eq := rfl
    selectedPivots_nonempty := hselectedNonempty
    selectedPivots_subset := hselectedSubset
    level_lt_bucketLoss := hlevelLt
    occupied_bucket_card_le_loss := by
      simpa only [positivePivots, levelOf] using hlabelCard
    clusterCard_bounds := hbounds
    retained_card_eq_cluster_sum := hretainedCard
    full_card_le_loss_mul_retained_card := by
      rw [hretainedCard]
      exact hfullNat
    selected_card_mul_scale_le_retained_card := by
      rw [hretainedCard]
      exact hlowerSum
    retained_card_le_selected_card_mul_twice_scale := by
      rw [hretainedCard]
      exact hupperSum
    retained_nonempty := hretainedNonempty }⟩

/-- Direct adapter from the callback-free two-stage geometric outcome to the
owner-cardinality dyadic refinement. -/
theorem exists_ownerCluster_dyadic_refinement_of_twoStage
    {alpha : Type u} [DecidableEq alpha]
    {vertices : Finset alpha}
    {rectangleAt : alpha ->
      FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1.C2GraphRectangle}
    {domain : Set Real}
    {center :
      FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1.C2GraphRectangle}
    {delta localScale referenceScale comparisonLambda curvatureRatio : Real}
    {weight : alpha -> ENNReal}
    (C : CompactC2TwoStageGreedyClusteringAtScalesOutcome vertices rectangleAt
      domain center delta localScale referenceScale comparisonLambda
        curvatureRatio weight)
    (hvertices : vertices.Nonempty) :
    Nonempty (OwnerClusterDyadicRefinement vertices C.pivots C.owner) := by
  apply exists_ownerCluster_dyadic_refinement vertices C.pivots C.owner
    hvertices
  simpa only [ownerClusterCard] using C.card_partition

#print axioms ownerClusterCard
#print axioms nonemptyOwnerPivots
#print axioms ownerClusterDyadicLevel
#print axioms ownerClusterDyadicPivots
#print axioms ownerClusterUnion
#print axioms ownerClusterBucketLoss
#print axioms OwnerClusterDyadicRefinement
#print axioms exists_ownerCluster_dyadic_refinement
#print axioms exists_ownerCluster_dyadic_refinement_of_twoStage

end

end FamilyStickyCinematicL32Lemma55OwnerClusterDyadicRefinementV1
