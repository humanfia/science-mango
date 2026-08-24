import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualTotalBucketPartitionV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketSumV1RepoV2

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosNonuniformBaselineStepV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketsV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualAnnularBucketSumV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLowBucketV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualTotalBucketPartitionV1

theorem nonuniform_total_length_le_baseline_step
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (hsymbolPow : Fintype.card symbol ≤ 2 ^ depth) :
    (∑ i : index, ((family i).order.length : Real)) ≤
      2 * paperBaseline depth symbol * (Fintype.card index : Real) +
        5 * paperStep index symbol * (Fintype.card index : Real) := by
  let L := Fintype.card index
  have hpartition := total_length_eq_low_add_annular family depth
  have hlow := lowBucketMass_le family depth
  have hannular := sum_actual_annularBucketMass_le
    family hreverse depth hdepth hsymbolPow L
  rw [hpartition]
  calc
    lowBucketMass family depth +
        ∑ k ∈ Finset.range L, annularBucketMass family depth k ≤
      (Fintype.card index : Real) *
          (paperBaseline depth symbol + paperStep index symbol) +
        (paperBaseline depth symbol * (Fintype.card index : Real) +
          4 * paperStep index symbol * (Fintype.card index : Real)) :=
      add_le_add hlow hannular
    _ = 2 * paperBaseline depth symbol * (Fintype.card index : Real) +
        5 * paperStep index symbol * (Fintype.card index : Real) := by ring

#print axioms nonuniform_total_length_le_baseline_step

end FamilyStickyCinematicL32Prop41MarcusTardosNonuniformBaselineStepV1
