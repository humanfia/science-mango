import ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling

/-!
# Thermalization consumer: exact coupling scaling of the actual cluster source

This consumer checks that the genuine canonical iid coercive full-cluster
source is exactly the finite sum over every left and right slot of its unit
quadratic and quartic defects, weighted by `kappa * g` and `beta * g^2`.
It also exposes the corresponding triangle-inequality bound by the explicit
finite sums of unit-slot norms.

Neither theorem asserts decay, RPA, nonresonance, Markov closure, or
recollision suppression.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling

noncomputable section

/-- Consumer alias: exact full-cluster coupling-resolved slot expansion. -/
theorem problem_canonical_actual_cluster_source_eq_coupling_unitSlotSums :
    type_of%
      (@canonicalCoerciveClusterFactorizationDefectSource_eq_coupling_unitSlotSums) :=
  @canonicalCoerciveClusterFactorizationDefectSource_eq_coupling_unitSlotSums

/-- Consumer alias: explicit finite-sum norm bound for the same source. -/
theorem problem_norm_canonical_actual_cluster_source_le_coupling_unitSlotNormSums :
    type_of%
      (@norm_canonicalCoerciveClusterFactorizationDefectSource_le_coupling_unitSlotNormSums) :=
  @norm_canonicalCoerciveClusterFactorizationDefectSource_le_coupling_unitSlotNormSums

#print axioms canonicalCoerciveClusterFactorizationDefectSource_eq_coupling_unitSlotSums
#print axioms
  norm_canonicalCoerciveClusterFactorizationDefectSource_le_coupling_unitSlotNormSums
#print axioms problem_canonical_actual_cluster_source_eq_coupling_unitSlotSums
#print axioms
  problem_norm_canonical_actual_cluster_source_le_coupling_unitSlotNormSums

end

end ArchonPhysicsConsumers.Thermalization
