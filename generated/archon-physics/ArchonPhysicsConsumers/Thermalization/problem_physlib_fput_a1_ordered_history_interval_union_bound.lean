import ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalUnionBound

/-!
# Thermalization consumer: deduplicated full-history small denominators

For a fixed linear actual A1 history, every recursive denominator occurrence
is covered by a distinct nonempty interval coordinate.  The compact-atlas
union bound therefore uses at most `r ^ 2` regular coefficients and charges
the union of compact complements once.

For a branching tree the displayed capacity is
`min (r! * (2 ^ r - 1)) (r! * r ^ 2)`.  Applying that bound still requires
an explicit `RandomBranchingA1IntervalFiberSelector`: its `covers` field
maps every branching occurrence to a genuine actual A1 interval chart, and
the separate capacity hypothesis certifies the deduplicated enumeration.
This consumer does not construct a common fiber across branches and assumes
no independence, re-Haar law, Markov/RPA closure, or recollision decay.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalUnionBound

noncomputable section

/-- Consumer alias for occurrence-to-interval coverage. -/
theorem problem_full_ordered_history_occurrences_are_interval_covered :
    type_of% (@physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_subset_intervals) :=
  @physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_subset_intervals

/-- Consumer alias for the explicit quadratic fixed-order linear bound. -/
theorem problem_measure_full_ordered_history_small_denominators_le_sq :
    type_of% (@measure_physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_le_sq) :=
  @measure_physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_le_sq

/-- Consumer alias for the explicit selector/fiber compatibility boundary. -/
theorem problem_measure_full_branching_history_selected_intervals :
    type_of% (@measure_randomBranchingSmallEvent_le_selectedIntervalCompactAtlas) :=
  @measure_randomBranchingSmallEvent_le_selectedIntervalCompactAtlas

/-- Consumer alias for the never-worse deduplicated branching capacity bound. -/
theorem problem_measure_full_branching_history_le_deduplicated_budget :
    type_of% (@measure_randomBranchingSmallEvent_le_deduplicatedIntervalBudget) :=
  @measure_randomBranchingSmallEvent_le_deduplicatedIntervalBudget

#print axioms card_orderedHistoryFiniteInterval_le_sq
#print axioms physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_subset_intervals
#print axioms measure_event_le_finiteCoordinateCompactAtlas
#print axioms measure_physlibA1OrderedHistoryRecursiveSmallDenominatorEvent_le_sq
#print axioms randomBranchingSelectedIntervalRegularCoefficient_le_deduplicated
#print axioms measure_randomBranchingSmallEvent_le_deduplicatedIntervalBudget
#print axioms problem_full_ordered_history_occurrences_are_interval_covered
#print axioms problem_measure_full_ordered_history_small_denominators_le_sq
#print axioms problem_measure_full_branching_history_selected_intervals
#print axioms problem_measure_full_branching_history_le_deduplicated_budget

end

end ArchonPhysicsConsumers.Thermalization
