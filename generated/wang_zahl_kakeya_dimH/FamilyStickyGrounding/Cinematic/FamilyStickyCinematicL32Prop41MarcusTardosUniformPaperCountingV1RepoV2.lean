import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosUniformCountingExplicitWeightsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPaperWeightBoundsV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosUniformPaperCountingV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosUniformCountingExplicitWeightsV1
open FamilyStickyCinematicL32Prop41MarcusTardosPaperWeightBoundsV1

/-!
# Fully internalized uniform Marcus--Tardos counting theorem

The exact source paper weights and all three of their aggregate estimates are
chosen internally.  The only mathematical inputs are the finite cyclic-list
family, pairwise intersection reversal, the common list length, and a dyadic
depth covering that length.
-/

theorem uniform_counting_eight_or_twentyone
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (d : Nat) (huniform : ∀ i, (family i).order.length = d)
    (hdpow : d ≤ 2 ^ depth) :
    (d : Real) ≤ 8 * (depth : Real) * Real.sqrt (Fintype.card symbol : Real) ∨
      (d : Real) ≤
        21 * (Fintype.card symbol : Real) /
          Real.sqrt (Fintype.card index : Real) := by
  exact uniform_counting_eight_or_twentyone_of_weight_bounds
    family hreverse depth hdepth d huniform hdpow
    (paperWeight depth)
    (paperWeight_pos depth)
    (paperWeight_sum_le_depth depth)
    (paperWeight_weighted_depth_sum_le_three_div depth hdepth)
    (paperWeight_reciprocal_sum_le_four_depth depth)

#print axioms uniform_counting_eight_or_twentyone

end FamilyStickyCinematicL32Prop41MarcusTardosUniformPaperCountingV1
