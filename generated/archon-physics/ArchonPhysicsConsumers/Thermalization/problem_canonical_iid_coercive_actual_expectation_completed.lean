import ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted

/-!
# Consumer: completed actual canonical iid expectation hierarchy

For every fixed finite family of nontranslation signed ordered modes on the
actual coercive alpha--beta canonical iid flow, the checked dependency now
contains explicit deterministic bounds for

* the signed interaction-picture amplitudes;
* the complete quadratic-plus-cubic rotated sources;
* every fixed finite signed block and its exact one-slot insertion.

The corresponding random variables are Bochner integrable and the time
derivative passes through the continuous canonical iid expectation with no
abstract envelope or base-integrability input.

This is an exact finite-volume higher-moment hierarchy backbone.  It does not
assert decay or closure of nonresonant/recollision/exceptional connected
sectors, does not kill charge-balanced resonant clusters, and does not infer
RPA, independence, Markov dynamics, or a kinetic limit.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted

#check inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope
#check norm_transformedNonlinearForce_le_envelope
#check norm_canonicalInteractionAmplitude_le_envelope_of_simple
#check norm_canonicalOrderedRotatedSource_le_envelope_of_simple
#check canonicalSignedBlockBounds_ae_allTime
#check integrable_canonicalSignedBlock_fixedTime
#check integrable_canonicalSignedBlockInsertion_fixedTime
#check hasCanonicalSignedBlockLocalDerivativeEnvelope_actual
#check hasDerivAt_canonicalSignedBlockBochnerIntegral_actual

#print axioms inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope
#print axioms norm_transformedNonlinearForce_le_envelope
#print axioms canonicalSignedBlockBounds_ae_allTime
#print axioms integrable_canonicalSignedBlock_fixedTime
#print axioms integrable_canonicalSignedBlockInsertion_fixedTime
#print axioms hasDerivAt_canonicalSignedBlockBochnerIntegral_actual

end ArchonPhysicsConsumers.Thermalization
