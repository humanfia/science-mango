import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1RepoV2
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketsV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1

/-! Literal disjoint annular buckets cut out by consecutive long-list tails. -/

noncomputable def annularBucket
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth level : Nat) : Finset index :=
  longIndex family depth level \ longIndex family depth (level + 1)

noncomputable def annularBucketMass
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth level : Nat) : Real :=
  ∑ i ∈ annularBucket family depth level, (family i).order.length

theorem paperThreshold_mono
    (depth : Nat) {k l : Nat} (hkl : k ≤ l)
    (index symbol : Type*) [Fintype index] [Fintype symbol] :
    paperThreshold depth k index symbol ≤
      paperThreshold depth l index symbol := by
  unfold paperThreshold
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hkl)
      (by
        dsimp [paperStep]
        positivity)) _

theorem annularBucket_subset_longIndex
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth level : Nat) :
    annularBucket family depth level ⊆ longIndex family depth level :=
  Finset.sdiff_subset

theorem annularBucket_card_cap
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (hsymbolPow : Fintype.card symbol ≤ 2 ^ depth)
    (level : Nat) :
    (4 : Real) ^ level * (annularBucket family depth level).card ≤
      (Fintype.card index : Real) := by
  have hcardNat := Finset.card_le_card
    (annularBucket_subset_longIndex family depth level)
  have hcard : ((annularBucket family depth level).card : Real) ≤
      (longIndex family depth level).card := by exact_mod_cast hcardNat
  calc
    (4 : Real) ^ level * (annularBucket family depth level).card ≤
        (4 : Real) ^ level * (longIndex family depth level).card :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ (Fintype.card index : Real) :=
      longIndex_card_cap family hreverse depth hdepth hsymbolPow level

theorem annularBucket_member_length_upper
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth level : Nat) {i : index}
    (hi : i ∈ annularBucket family depth level) :
    ((family i).order.length : Real) ≤
      paperThreshold depth (level + 1) index symbol := by
  have hnot : i ∉ longIndex family depth (level + 1) :=
    (Finset.mem_sdiff.mp hi).2
  have hnotlt : ¬ paperThreshold depth (level + 1) index symbol <
      ((family i).order.length : Real) := by
    intro hlt
    apply hnot
    simp [longIndex, hlt]
  exact le_of_not_gt hnotlt

theorem annularBucketMass_le
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth level : Nat) :
    annularBucketMass family depth level ≤
      (annularBucket family depth level).card *
        (paperBaseline depth symbol +
          (2 : Real) ^ (level + 1) * paperStep index symbol) := by
  calc
    annularBucketMass family depth level ≤
        ∑ _i ∈ annularBucket family depth level,
          paperThreshold depth (level + 1) index symbol := by
      exact Finset.sum_le_sum fun i hi ↦
        annularBucket_member_length_upper family depth level hi
    _ = (annularBucket family depth level).card *
        (paperBaseline depth symbol +
          (2 : Real) ^ (level + 1) * paperStep index symbol) := by
      simp [paperThreshold]
      ring

theorem annularBucket_disjoint_of_lt
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth : Nat) {k l : Nat} (hkl : k < l) :
    Disjoint (annularBucket family depth k)
      (annularBucket family depth l) := by
  apply Finset.disjoint_left.2
  intro i hik hil
  have hiknot : i ∉ longIndex family depth (k + 1) :=
    (Finset.mem_sdiff.mp hik).2
  have hillong : i ∈ longIndex family depth l :=
    (Finset.mem_sdiff.mp hil).1
  have hlen : paperThreshold depth l index symbol <
      ((family i).order.length : Real) :=
    (Finset.mem_filter.mp hillong).2
  have hmono : paperThreshold depth (k + 1) index symbol ≤
      paperThreshold depth l index symbol :=
    paperThreshold_mono depth (Nat.succ_le_of_lt hkl) index symbol
  apply hiknot
  simp [longIndex, hmono.trans_lt hlen]

theorem annularBuckets_pairwiseDisjoint
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth L : Nat) :
    ((Finset.range L : Finset Nat) : Set Nat).PairwiseDisjoint
      (annularBucket family depth) := by
  intro k hk l hl hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · exact annularBucket_disjoint_of_lt family depth hkl
  · exact (annularBucket_disjoint_of_lt family depth hlk).symm

theorem sum_annularBucket_card_le
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth L : Nat) :
    (∑ k ∈ Finset.range L,
      (annularBucket family depth k).card) ≤ Fintype.card index := by
  calc
    (∑ k ∈ Finset.range L,
        (annularBucket family depth k).card) =
        ((Finset.range L).biUnion (annularBucket family depth)).card := by
      exact (Finset.card_biUnion
        (annularBuckets_pairwiseDisjoint family depth L)).symm
    _ ≤ (Finset.univ : Finset index).card := by
      exact Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card index := Finset.card_univ

#print axioms paperThreshold_mono
#print axioms annularBucket_card_cap
#print axioms annularBucketMass_le
#print axioms sum_annularBucket_card_le

end FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketsV1
