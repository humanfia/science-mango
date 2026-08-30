import ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy

/-!
# Consumer: continuous canonical iid expectation hierarchy

This consumer locks the continuous-expectation frontier at arbitrary fixed
finite order.

The kernel-checked part now contains:

* one almost-sure set on which the true coercive alpha--beta canonical orbit
  stays in its common energy shell for every real time;
* a deterministic `omega⁻¹ <= N` bound for every fixed nontranslation ordered
  mode;
* differentiation of the genuine canonical block Bochner integral into the
  genuine full one-slot source integral, under the explicit local derivative
  envelope and base-time integrability premises.

The last two premises are not claimed to follow automatically merely from
pointwise differentiability.  The remaining concrete adapter is to turn the
shell and inverse-frequency controls into a norm bound for the full
quadratic-plus-cubic source and its finite block products.  No zero mode,
resonant sector, RPA, Markov closure, or decay statement is discarded.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.RandomMassPositiveCollisionData

#check norm_canonicalRandomMassPhaseTrajectory_le_cutoffRadius_ae_allTime
#check norm_canonicalFlowPosition_le_cutoffRadius_ae_allTime
#check norm_canonicalFlowMomentum_le_cutoffRadius_ae_allTime
#check inv_canonicalOrderedFrequency_le_volume
#check HasCanonicalSignedBlockLocalDerivativeEnvelope
#check integrable_const_of_hasCanonicalSignedBlockLocalDerivativeEnvelope
#check hasDerivAt_canonicalSignedBlockBochnerIntegral

#print axioms norm_canonicalRandomMassPhaseTrajectory_le_cutoffRadius_ae_allTime
#print axioms norm_canonicalFlowPosition_le_cutoffRadius_ae_allTime
#print axioms norm_canonicalFlowMomentum_le_cutoffRadius_ae_allTime
#print axioms inv_canonicalOrderedFrequency_le_volume
#print axioms hasDerivAt_canonicalSignedBlockBochnerIntegral

end ArchonPhysicsConsumers.Thermalization
