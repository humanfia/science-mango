import ArchonPhysics.PhyslibFPUTActualBranchingA1CompactSmallBall

/-!
# Thermalization consumer: actual branching heterogeneous small balls

This consumer checks the quantitative endpoint for genuine decorated FPUT
branching histories.  Different denominator occurrences may retain different
mass pairs, and vertices inside one cumulative interval may have different
observed output modes.

For each selected interval, an explicitly compact good set must lie in the
actual differentiability source, and the total actual vertical Jacobian must
obey a displayed positive lower bound.  Those hypotheses construct the
finite inverse-function atlases; measurability and the 5/2 one-site density
are derived.

The resulting full branching bad-event estimate is linear in the threshold,
up to one probability of the union of compact complements.  Its finite
coefficient costs at most order! times order squared copies of the derived
largest atlas coefficient.  No theorem here derives the Jacobian lower bound
from random masses, and there is no initial-phase independence, re-Haar,
Markov/RPA closure, or recollision decay.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PhyslibFPUTActualBranchingA1CompactSmallBall

noncomputable section

/-- Consumer alias: the heterogeneous interval derivative is its actual
vertical Jacobian sum. -/
theorem problem_actual_branching_heterogeneous_deriv_eq_sum :
    type_of% (@hasStrictDerivAt_actualA1VertexIntervalPairMismatchFiber) :=
  @hasStrictDerivAt_actualA1VertexIntervalPairMismatchFiber

/-- Consumer alias: compactness plus the honest total-Jacobian lower bound
constructs one quantitative heterogeneous interval atlas. -/
theorem problem_actual_branching_heterogeneous_compact_atlas :
    type_of% (@exists_atlasCard_actualA1VertexIntervalPairFiberCompact) :=
  @exists_atlasCard_actualA1VertexIntervalPairFiberCompact

/-- Consumer alias: algebraic actual coverage implies finite small-denominator
coverage for the full branching event. -/
theorem problem_actual_branching_small_event_finite_cover :
    type_of% (@actualA1BranchingSmallDenominatorEvent_subset_finite) :=
  @actualA1BranchingSmallDenominatorEvent_subset_finite

/-- Consumer alias: supplied occurrence atlases give the exact summed
coefficient plus one compact-bad-event probability. -/
theorem problem_actual_branching_small_event_compact_atlas :
    type_of% (@measure_actualA1BranchingSmallDenominatorEvent_le_compactAtlas) :=
  @measure_actualA1BranchingSmallDenominatorEvent_le_compactAtlas

/-- Consumer alias: the finite coefficient sum has the explicit factorial
and quadratic fixed-order count. -/
theorem problem_actual_branching_atlas_coefficient_factorial_sq :
    type_of% (@actualA1BranchingCompactAtlasRegularCoefficient_le_factorial_sq) :=
  @actualA1BranchingCompactAtlasRegularCoefficient_le_factorial_sq

/-- Consumer alias: every occurrence atlas is constructed from its displayed
compact regular set and total-Jacobian lower bound. -/
theorem problem_actual_branching_occurrence_atlases_exist :
    type_of% (@exists_actualA1BranchingOccurrenceCompactAtlasCertificates) :=
  @exists_actualA1BranchingOccurrenceCompactAtlasCertificates

/-- Consumer alias: final linear-threshold probability bound with the
order! times order squared count. -/
theorem problem_actual_branching_small_event_factorial_sq :
    type_of% (@exists_measure_actualA1BranchingSmallDenominatorEvent_le_factorial_sq) :=
  @exists_measure_actualA1BranchingSmallDenominatorEvent_le_factorial_sq

#print axioms measurable_actualA1VertexIntervalPairMismatchChart
#print axioms hasStrictDerivAt_actualA1VertexIntervalPairMismatchFiber
#print axioms exists_actualA1VertexIntervalPairFiber_localInjectivePatch
#print axioms exists_atlasCard_actualA1VertexIntervalPairFiberCompact
#print axioms exists_ordinaryGardenCoordinateCompactAtlas_of_actualA1Interval
#print axioms actualA1BranchingSmallDenominatorEvent_subset_finite
#print axioms measure_actualA1BranchingSmallDenominatorEvent_le_compactAtlas
#print axioms actualA1BranchingCompactAtlasRegularCoefficient_le_factorial_sq
#print axioms ordinaryGardenCoefficient_eq_atlasCard_mul_jacobian
#print axioms exists_actualA1BranchingOccurrenceCompactAtlasCertificates
#print axioms exists_measure_actualA1BranchingSmallDenominatorEvent_le_factorial_sq
#print axioms problem_actual_branching_heterogeneous_deriv_eq_sum
#print axioms problem_actual_branching_heterogeneous_compact_atlas
#print axioms problem_actual_branching_small_event_finite_cover
#print axioms problem_actual_branching_small_event_compact_atlas
#print axioms problem_actual_branching_atlas_coefficient_factorial_sq
#print axioms problem_actual_branching_occurrence_atlases_exist
#print axioms problem_actual_branching_small_event_factorial_sq

end

end ArchonPhysicsConsumers.Thermalization
