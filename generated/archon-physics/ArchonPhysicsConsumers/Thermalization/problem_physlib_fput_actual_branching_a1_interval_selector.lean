import ArchonPhysics.PhyslibFPUTActualBranchingA1IntervalSelector

/-!
# Thermalization consumer: actual branching A1 interval selector

This consumer checks the algebraic part of the missing branching interface.
A decorated FPUT binary tree is lifted to metadata-preserving linear
extensions whose entries retain the output mode, both child modes, and both
phase signs.  Every denominator occurrence is exactly a contiguous interval
sum of those genuine local A1 mismatches.  The finite selector has at most
`order! * order^2` coordinates.

Retained mass pairs may depend on the occurrence.  For the old
single-parameter style of covers, the explicit `realizes` condition says
that every occurrence-specific pair chart reconstructs the same displayed
mass path.  No common pair is silently assumed.

The earlier `RandomBranchingA1IntervalFiberSelector` also forces one
`observed` output mode across every selected interval.  Actual branching
histories need not satisfy that: the two-vertex obstruction and the exact
homogeneous-output adapter below expose the boundary.  After algebraic
coverage, the remaining analytic input is a positive lower bound on each
heterogeneous interval's sum of actual vertical Jacobians on its own compact
set.  This consumer proves no such global bound and assumes no initial phase
independence, re-Haar law, Markov/RPA closure, or recollision decay.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PhyslibFPUTActualBranchingA1IntervalSelector

noncomputable section

/-- Consumer alias: a decorated node is a genuine quadratic A1 mismatch. -/
theorem problem_actual_branching_node_is_A1_mismatch :
    type_of% (@mismatch_randomEigenmodeBinaryNodeA1Vertex) :=
  @mismatch_randomEigenmodeBinaryNodeA1Vertex

/-- Consumer alias: forgetting metadata recovers the established scalar
branching linear extensions exactly. -/
theorem problem_actual_branching_metadata_forgetful_map :
    type_of% (@map_randomEigenmodeBinaryTreeA1VertexLinearExtensions) :=
  @map_randomEigenmodeBinaryTreeA1VertexLinearExtensions

/-- Consumer alias: every actual branching occurrence has a genuine
heterogeneous contiguous-interval representation. -/
theorem problem_actual_branching_occurrence_is_A1_interval :
    type_of% (@exists_actualA1VertexInterval_eq_branchingHistoryDenominator) :=
  @exists_actualA1VertexInterval_eq_branchingHistoryDenominator

/-- Consumer alias: the finite interval selector covers all occurrences. -/
theorem problem_actual_branching_finite_selector_covers :
    type_of% (@exists_actualA1BranchingIntervalIndex_eq_denominator) :=
  @exists_actualA1BranchingIntervalIndex_eq_denominator

/-- Consumer alias: explicit factorial-times-quadratic selector capacity. -/
theorem problem_actual_branching_finite_selector_capacity :
    type_of% (@card_actualA1BranchingIntervalIndex_le) :=
  @card_actualA1BranchingIntervalIndex_le

/-- Consumer alias: retained pairs may vary occurrence by occurrence at a
fixed frozen realization. -/
theorem problem_actual_branching_occurrence_dependent_pair_covers :
    type_of% (@exists_actualA1BranchingOccurrenceFiberValue_eq_denominator) :=
  @exists_actualA1BranchingOccurrenceFiberValue_eq_denominator

/-- Consumer alias: every occurrence-specific pair chart reconstructing a
common mass path is exactly its direct actual interval mismatch. -/
theorem problem_actual_branching_fiber_coordinate_eq_actual :
    type_of% (@actualA1BranchingOccurrenceFiberCoordinate_eq_actual) :=
  @actualA1BranchingOccurrenceFiberCoordinate_eq_actual

/-- Consumer alias: literal all-parameter covers statement for the genuine
heterogeneous coordinates. -/
theorem problem_actual_branching_fiber_family_covers :
    type_of% (@actualA1BranchingOccurrenceFiberCoordinate_covers) :=
  @actualA1BranchingOccurrenceFiberCoordinate_covers

/-- Consumer alias: differing vertex outputs obstruct a faithful single
observed-mode encoding of even a two-vertex history. -/
theorem problem_actual_branching_fixed_observed_obstruction :
    type_of% (@not_observedHomogeneous_pair) :=
  @not_observedHomogeneous_pair

/-- Consumer alias: homogeneous-output blocks reduce exactly to the previous
fixed-observed interval chart. -/
theorem problem_actual_branching_homogeneous_adapter :
    type_of% (@actualA1VertexIntervalPairMismatchChart_eq_fixedObserved) :=
  @actualA1VertexIntervalPairMismatchChart_eq_fixedObserved

#print axioms mismatch_randomEigenmodeBinaryNodeA1Vertex
#print axioms map_randomEigenmodeBinaryTreeA1VertexLinearExtensions
#print axioms exists_actualA1VertexInterval_eq_branchingHistoryDenominator
#print axioms exists_actualA1BranchingIntervalIndex_eq_denominator
#print axioms card_actualA1BranchingIntervalIndex_le
#print axioms exists_actualA1BranchingOccurrenceFiberValue_eq_denominator
#print axioms actualA1BranchingOccurrenceFiberCoordinate_eq_actual
#print axioms actualA1BranchingOccurrenceFiberCoordinate_covers
#print axioms ActualA1BranchingOccurrenceJacobianNoncancellation
#print axioms not_observedHomogeneous_pair
#print axioms actualA1VertexIntervalPairMismatchChart_eq_fixedObserved
#print axioms problem_actual_branching_node_is_A1_mismatch
#print axioms problem_actual_branching_metadata_forgetful_map
#print axioms problem_actual_branching_occurrence_is_A1_interval
#print axioms problem_actual_branching_finite_selector_covers
#print axioms problem_actual_branching_finite_selector_capacity
#print axioms problem_actual_branching_occurrence_dependent_pair_covers
#print axioms problem_actual_branching_fiber_coordinate_eq_actual
#print axioms problem_actual_branching_fiber_family_covers
#print axioms problem_actual_branching_fixed_observed_obstruction
#print axioms problem_actual_branching_homogeneous_adapter

end

end ArchonPhysicsConsumers.Thermalization
