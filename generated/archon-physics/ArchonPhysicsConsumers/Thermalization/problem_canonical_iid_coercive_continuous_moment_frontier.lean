import ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
import ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation

/-!
Consumer certificate for the continuous canonical iid signed modal frontier.

The checked endpoint has arbitrary fixed finite order, uses the actual
canonical coercive alpha--beta flow, and has a time-uniform almost-sure set
for the pointwise block hierarchy.  The continuous block moments and
connected cumulant are concrete Bochner-integral definitions.  This consumer
does not claim derivative-under-integral: the uniform integrable source bound
listed in the core documentation remains to be proved.

The checked arbitrary-cluster propagation API supplies the exact finite
telescope once its source-defect bounds apply.  This consumer does not claim
that the canonical continuous initial Bochner expressions have already been
identified with its initial-Haar interface.
-/

open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge

#check measurable_canonicalInteractionAmplitude
#check measurable_canonicalSignedBlockObservable
#check hasDerivAt_orderedSignedInteractionPath
#check hasDerivAt_canonicalInteractionAmplitude_of_simple
#check canonicalSignedBlockHierarchy_ae_allTime
#check measurable_canonicalSignedBlockInsertion
#check canonicalSignedBlockBochnerIntegral
#check canonicalSignedConnectedCumulant
#check canonicalSignedConnectedCumulantHierarchySource
#check orderedClusterFactorizationDefect_zero_of_initialHaar
#check norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le

#print axioms measurable_canonicalInteractionAmplitude
#print axioms hasDerivAt_orderedSignedInteractionPath
#print axioms hasDerivAt_canonicalInteractionAmplitude_of_simple
#print axioms canonicalSignedBlockHierarchy_ae_allTime
#print axioms measurable_canonicalSignedBlockInsertion
#print axioms aestronglyMeasurable_canonicalSignedBlockInsertion_fixedTime
