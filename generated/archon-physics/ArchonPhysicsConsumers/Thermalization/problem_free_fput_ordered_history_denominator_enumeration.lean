import ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration

/-!
Consumer audit for the exact all-order ordered-history denominator list.
-/

open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration

example (gamma : Real) (phases : List Real) :
    FullyNonresonantOrderedHistory gamma phases ↔
      ∀ delta ∈ orderedHistoryDenominators phases, gamma ≤ |delta| :=
  fullyNonresonantOrderedHistory_iff_forall_mem_denominators gamma phases

example (gamma : Real) (phases : List Real) :
    ¬ FullyNonresonantOrderedHistory gamma phases ↔
      ∃ delta ∈ orderedHistoryDenominators phases, |delta| < gamma :=
  not_fullyNonresonantOrderedHistory_iff_exists_small_denominator gamma phases

example (phases : List Real) :
    (orderedHistoryDenominators phases).length + 1 = 2 ^ phases.length :=
  length_orderedHistoryDenominators_add_one phases

example (gamma : Real) (phases : List Real) :
    (smallOrderedHistoryDenominators gamma phases).card ≤
      2 ^ phases.length - 1 :=
  card_smallOrderedHistoryDenominators_le gamma phases

#print axioms fullyNonresonantOrderedHistory_iff_forall_mem_denominators
#print axioms not_fullyNonresonantOrderedHistory_iff_exists_small_denominator
#print axioms length_orderedHistoryDenominators_add_one
#print axioms length_orderedHistoryDenominators
#print axioms smallOrderedHistoryDenominators_nonempty_iff
#print axioms card_smallOrderedHistoryDenominators_le
