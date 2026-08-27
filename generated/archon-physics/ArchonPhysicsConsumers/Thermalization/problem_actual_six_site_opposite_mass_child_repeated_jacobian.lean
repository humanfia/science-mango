import ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedJacobian

namespace ArchonPhysicsConsumers.Thermalization
open ArchonPhysics

open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedJacobian
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open Set

noncomputable section

/-- Consumer-facing exact seed with full simple spectrum and the nonzero
true two-dimensional raw-mass frequency Jacobian required by the regular
spectral patch bridge. -/
example :
    ∃ s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6),
      oppositeChildRepeatedMismatch s = 0 ∧
      SimpleOrderedSpectrum (oppositeSixSiteHarmonic s) ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 0 ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 3 ∧
      (actualTwoMassChildFrequencyJacobian frozenUnitMassSix
        (0 : Lattice.Site 6) (3 : Lattice.Site 6) 0 3
        (oppositeMassPair s)).det ≠ 0 :=
  exists_interior_simple_positive_jacobian_oppositeChildRepeated_exactResonance

#print axioms
  ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedJacobian.exists_interior_simple_positive_jacobian_oppositeChildRepeated_exactResonance

end

end ArchonPhysicsConsumers.Thermalization
