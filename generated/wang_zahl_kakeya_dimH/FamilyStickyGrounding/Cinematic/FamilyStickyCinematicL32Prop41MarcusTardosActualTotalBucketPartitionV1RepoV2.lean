import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualTerminalBucketEmptyV1RepoV2

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualTotalBucketPartitionV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketsV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLowBucketV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualBucketTelescopingCoverV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualTerminalBucketEmptyV1

theorem lowBucket_disjoint_bucketUnion
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth L : Nat) :
    Disjoint (lowBucket family depth)
      ((Finset.range L).biUnion (annularBucket family depth)) := by
  apply Finset.disjoint_left.2
  intro i hilow hiunion
  have hinot : i ∉ longIndex family depth 0 :=
    (Finset.mem_sdiff.mp hilow).2
  rcases Finset.mem_biUnion.mp hiunion with ⟨k, hk, hibucket⟩
  have hilongk : i ∈ longIndex family depth k :=
    (Finset.mem_sdiff.mp hibucket).1
  have hlen : paperThreshold depth k index symbol <
      ((family i).order.length : Real) :=
    (Finset.mem_filter.mp hilongk).2
  have hmono : paperThreshold depth 0 index symbol ≤
      paperThreshold depth k index symbol :=
    paperThreshold_mono depth (Nat.zero_le k) index symbol
  apply hinot
  simp [longIndex, hmono.trans_lt hlen]

theorem total_length_eq_low_add_annular
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth : Nat) :
    (∑ i : index, ((family i).order.length : Real)) =
      lowBucketMass family depth +
        ∑ k ∈ Finset.range (Fintype.card index),
          annularBucketMass family depth k := by
  let L := Fintype.card index
  have hcover : lowBucket family depth ∪
      (Finset.range L).biUnion (annularBucket family depth) = Finset.univ := by
    have hc := bucket_cover_with_terminal family depth L
    rw [terminal_longIndex_empty family depth] at hc
    simpa using hc
  calc
    (∑ i : index, ((family i).order.length : Real)) =
        ∑ i ∈ lowBucket family depth ∪
            (Finset.range L).biUnion (annularBucket family depth),
          ((family i).order.length : Real) := by rw [hcover]
    _ = lowBucketMass family depth +
        ∑ i ∈ (Finset.range L).biUnion (annularBucket family depth),
          ((family i).order.length : Real) := by
      rw [Finset.sum_union (lowBucket_disjoint_bucketUnion family depth L)]
      rfl
    _ = lowBucketMass family depth +
        ∑ k ∈ Finset.range L,
          annularBucketMass family depth k := by
      rw [Finset.sum_biUnion
        (annularBuckets_pairwiseDisjoint family depth L)]
      rfl

#print axioms lowBucket_disjoint_bucketUnion
#print axioms total_length_eq_low_add_annular

end FamilyStickyCinematicL32Prop41MarcusTardosActualTotalBucketPartitionV1
