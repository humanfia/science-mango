import ArchonPhysics.ActualSixSiteNearResonantFixedCollisionWeightWitness

/-!
# Consumer: positive six-site near-resonant collision weight

This acceptance theorem projects the concrete finite elimination certificate
to the scientific payload needed downstream: arbitrarily small positive
near-resonance together with a strictly positive normalized interaction
weight.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantFiniteCollisionEliminationCertificate
open ArchonPhysics.ActualSixSiteNearResonantFixedCollisionWeightWitness
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic

noncomputable section

theorem problem_actualSixSiteNearResonant_positiveNormalizedCollisionWeight
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ t : Real,
      0 < t ∧
      abs (actualSixSiteNearResonantMismatchPath t) < epsilon ∧
      0 < harmonicOrderedNormalizedInteractionWeight
        (actualSixSiteThreeMassConfig (nearResonantMassTriple t))
        cleanSixSiteDecayModes := by
  rcases
      exists_actualSixSiteNearResonant_weightedJacobianWitness_of_finiteCertificate
        hepsilon with
    ⟨t, ht, _hsupport, hmismatch, _hsimple, _hjacobian, hweight⟩
  exact ⟨t, ht, hmismatch, hweight⟩

#check harmonicOrderedNormalizedInteractionWeight_oneTenth_pos

#print axioms harmonicOrderedNormalizedInteractionWeight_oneTenth_pos
#print axioms
  problem_actualSixSiteNearResonant_positiveNormalizedCollisionWeight

end

end ArchonPhysicsConsumers.Thermalization
