import ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedCollisionWeight

/-!
# Consumer: exact six-site child-repeated collision-weight no-go

The unconditional opposite-site exact resonance has a regular two-mass
frequency chart and a positive linear mismatch small-ball slope, but its
corresponding physical parent-child-child cubic weight is killed exactly by
bond-reflection symmetry.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedCollisionWeight
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector

noncomputable section

/-- Exact boundary of the six-site seed: resonance, simple spectrum, and
positive participating frequencies coexist with zero normalized physical
cubic collision weight. -/
theorem problem_actual_six_site_exact_child_repeated_collision_weight_no_go :
    ∃ s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6),
      oppositeChildRepeatedMismatch s = 0 ∧
      SimpleOrderedSpectrum (oppositeSixSiteHarmonic s) ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 0 ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 3 ∧
      harmonicOrderedNormalizedInteractionWeight
        (oppositeSixSiteMassConfig s) oppositeChildRepeatedModes = 0 :=
  exists_oppositeSixSite_exactChildRepeated_resonance_weight_eq_zero

#print axioms
  harmonicOrderedNormalizedInteractionWeight_oppositeChildRepeated_eq_zero
#print axioms problem_actual_six_site_exact_child_repeated_collision_weight_no_go

end

end ArchonPhysicsConsumers.Thermalization
