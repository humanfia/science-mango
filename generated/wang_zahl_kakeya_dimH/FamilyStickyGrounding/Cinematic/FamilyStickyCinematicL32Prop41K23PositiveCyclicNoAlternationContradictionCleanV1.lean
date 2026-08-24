import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41K23PositiveCyclicPermutationKernelDecideV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41K23PositiveCyclicNoAlternationContradictionCleanV1

open FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1
open FamilyStickyCinematicL32Prop41K23PositiveCyclicPermutationKernelDecideV1
open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1

noncomputable section

theorem false_of_positiveCyclic_and_noAlternation
    (S : SixSeparatedIntervals)
    (hcyclic : forall h, HostCyclicPositive S.rank h)
    (hnoHost : ¬ AlternatingFour S.rank (fun e => e.1))
    (hnoNeighbor : ¬ AlternatingFour S.rank (fun e => e.2)) : False := by
  have hcyclicEquiv : forall h,
      HostCyclicPositive S.rankData.rankEquiv h := by
    simpa [SixSeparatedIntervals.rank] using hcyclic
  rcases alternating_host_or_neighbor_of_positive_cyclic_order
      S.rankData.rankEquiv hcyclicEquiv with hhost | hneighbor
  · apply hnoHost
    simpa [SixSeparatedIntervals.rank] using hhost
  · apply hnoNeighbor
    simpa [SixSeparatedIntervals.rank] using hneighbor

#print axioms false_of_positiveCyclic_and_noAlternation

end


end FamilyStickyCinematicL32Prop41K23PositiveCyclicNoAlternationContradictionCleanV1
