import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCorollarySixBucketingNumericsV1

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketSumV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketsV1
open FamilyStickyCinematicL32Prop41MarcusTardosCorollarySixBucketingNumericsV1

/-! The numerical Corollary summation instantiated with literal buckets. -/

theorem sum_actual_annularBucketMass_le
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (hsymbolPow : Fintype.card symbol ≤ 2 ^ depth)
    (L : Nat) :
    (∑ k ∈ Finset.range L, annularBucketMass family depth k) ≤
      paperBaseline depth symbol * (Fintype.card index : Real) +
        4 * paperStep index symbol * (Fintype.card index : Real) := by
  apply bucket_mass_sum_le_baseline_mul_add_four_step_mul
    L
    (fun k ↦ ((annularBucket family depth k).card : Real))
    (fun k ↦ annularBucketMass family depth k)
    (Fintype.card index : Real)
    (paperBaseline depth symbol)
    (paperStep index symbol)
  · positivity
  · dsimp [paperBaseline]
    positivity
  · dsimp [paperStep]
    positivity
  · exact_mod_cast sum_annularBucket_card_le family depth L
  · intro k hk
    exact annularBucket_card_cap
      family hreverse depth hdepth hsymbolPow k
  · intro k hk
    exact annularBucketMass_le family depth k

#print axioms sum_actual_annularBucketMass_le

end FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketSumV1
