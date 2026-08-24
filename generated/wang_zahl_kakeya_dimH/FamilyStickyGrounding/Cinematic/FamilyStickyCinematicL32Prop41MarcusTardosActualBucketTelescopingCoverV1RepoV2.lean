import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLowBucketV1RepoV2

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualBucketTelescopingCoverV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketsV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLowBucketV1

theorem bucket_cover_with_terminal
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth L : Nat) :
    (lowBucket family depth ∪
        (Finset.range L).biUnion (annularBucket family depth)) ∪
      longIndex family depth L = Finset.univ := by
  induction L with
  | zero =>
      ext i
      simp [lowBucket]
  | succ L ih =>
      apply Finset.Subset.antisymm (Finset.subset_univ _) ?_
      intro i hi
      have hiprev : i ∈
          (lowBucket family depth ∪
              (Finset.range L).biUnion (annularBucket family depth)) ∪
            longIndex family depth L := by
        rw [ih]
        simp
      rcases Finset.mem_union.mp hiprev with hcovered | htail
      · rcases Finset.mem_union.mp hcovered with hlow | hold
        · apply Finset.mem_union_left
          exact Finset.mem_union_left _ hlow
        · rcases Finset.mem_biUnion.mp hold with ⟨k, hk, hik⟩
          apply Finset.mem_union_left
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          exact ⟨k, Finset.mem_range.mpr
            ((Finset.mem_range.mp hk).trans (Nat.lt_succ_self L)), hik⟩
      · by_cases hnext : i ∈ longIndex family depth (L + 1)
        · exact Finset.mem_union_right _ hnext
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          refine ⟨L, Finset.mem_range.mpr (Nat.lt_succ_self L), ?_⟩
          exact Finset.mem_sdiff.mpr ⟨htail, hnext⟩

#print axioms bucket_cover_with_terminal

end FamilyStickyCinematicL32Prop41MarcusTardosActualBucketTelescopingCoverV1
