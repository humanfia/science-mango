import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketSumV1RepoV2
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLowBucketV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1

noncomputable def lowBucket
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth : Nat) : Finset index :=
  Finset.univ \ longIndex family depth 0

noncomputable def lowBucketMass
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth : Nat) : Real :=
  ∑ i ∈ lowBucket family depth, (family i).order.length

theorem lowBucketMass_le
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth : Nat) :
    lowBucketMass family depth ≤
      (Fintype.card index : Real) *
        (paperBaseline depth symbol + paperStep index symbol) := by
  have hterm (i : index) (hi : i ∈ lowBucket family depth) :
      ((family i).order.length : Real) ≤
        paperBaseline depth symbol + paperStep index symbol := by
    have hnot : i ∉ longIndex family depth 0 :=
      (Finset.mem_sdiff.mp hi).2
    have hnotlt : ¬ paperThreshold depth 0 index symbol <
        ((family i).order.length : Real) := by
      intro hlt
      apply hnot
      simp [longIndex, hlt]
    simpa [paperThreshold] using le_of_not_gt hnotlt
  calc
    lowBucketMass family depth ≤
        ∑ _i ∈ lowBucket family depth,
          (paperBaseline depth symbol + paperStep index symbol) := by
      exact Finset.sum_le_sum hterm
    _ = (lowBucket family depth).card *
        (paperBaseline depth symbol + paperStep index symbol) := by
      simp
      ring
    _ ≤ (Fintype.card index : Real) *
        (paperBaseline depth symbol + paperStep index symbol) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.card_le_univ (lowBucket family depth)
      · dsimp [paperBaseline, paperStep]
        positivity

#print axioms lowBucketMass_le

end FamilyStickyCinematicL32Prop41MarcusTardosActualLowBucketV1
