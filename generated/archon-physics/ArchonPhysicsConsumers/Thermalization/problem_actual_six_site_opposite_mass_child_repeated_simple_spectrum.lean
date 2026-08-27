import ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open Set

noncomputable section

/-- Consumer-facing certificate: the physical six-site opposite-mass slice
contains an interior exact child-repeated resonance with full simple spectrum
and positive selected modes. -/
example :
    ∃ s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6),
      oppositeChildRepeatedMismatch s = 0 ∧
      SimpleOrderedSpectrum (oppositeSixSiteHarmonic s) ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 0 ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 3 :=
  exists_interior_simple_positive_oppositeChildRepeated_exactResonance

#print axioms
  ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum.exists_interior_simple_positive_oppositeChildRepeated_exactResonance

end

end ArchonPhysicsConsumers.Thermalization
