import ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyArbitraryOrderClusterClosure

/-!
# Thermalization consumer: explicit-energy arbitrary-order cluster closure

This consumer verifies the fixed-order ordered-cluster telescope with
automatic moment bounds from `g_n -> 0` and exact empty-block normalization.
The general endpoint retains prefix binary convergence explicitly.  Its
kinetic-time specialization still requires, at every prefix, disjointness,
quadratic/quartic channel bounds, decay of the initial annealed covariance,
and decay of the coupling-weighted channel budget.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyArbitraryOrderClusterClosure

noncomputable section

/-- Consumer alias: automatic moment control plus explicit binary decay. -/
theorem problem_canonical_explicit_energy_arbitrary_order_cluster_closure :
    type_of%
      (@tendsto_orderedCanonicalSignedClusterFactorizationDefect_zero_of_tendsto_coupling_zero) :=
  @tendsto_orderedCanonicalSignedClusterFactorizationDefect_zero_of_tendsto_coupling_zero

/-- Consumer alias: kinetic-time closure with initial covariance and channel
decay retained as separate hypotheses. -/
theorem problem_canonical_explicit_energy_arbitrary_order_cluster_closure_of_initial_and_channels :
    type_of%
      (@canonicalHigherOrderRPA_tendsto_zero_at_kineticTime) :=
  @canonicalHigherOrderRPA_tendsto_zero_at_kineticTime

#print axioms
  tendsto_orderedCanonicalSignedClusterFactorizationDefect_zero_of_tendsto_coupling_zero
#print axioms
  canonicalHigherOrderRPA_tendsto_zero_at_kineticTime
#print axioms problem_canonical_explicit_energy_arbitrary_order_cluster_closure
#print axioms
  problem_canonical_explicit_energy_arbitrary_order_cluster_closure_of_initial_and_channels

end

end ArchonPhysicsConsumers.Thermalization
