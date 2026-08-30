import ArchonPhysics.RandomMassTwoPointProjectiveMarkov

/-!
# Consumer: two-point projective Feller prerequisite certificate

For two distinct masses in the frozen support and a positive spectral
parameter, this consumer exposes the exact algebraic and topological data now
available for the equal-weight two-atom transfer law: a noncompact relative
subgroup element, projective strong irreducibility, continuous normalized
actions, a continuous Markov operator, and compactness of its probability-law
state space.

The certificate contains neither a stationary measure nor a Furstenberg
positivity theorem.  In particular it does not assert a positive quenched
Lyapunov exponent, EFC, or localization.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassTransferProjectiveStrongIrreducibility
open ArchonPhysics.RandomMassTwoPointProjectiveMarkov

noncomputable section

/-- Frozen-support specialization of the algebraic plus Feller/compactness
prerequisites for the equal-weight two-point transfer law. -/
theorem frozen_twoMass_projective_Feller_prerequisite_certificate
    {lambda mass0 mass1 : Real} (hlambda : 0 < lambda)
    (hmass0 : mass0 ∈ RandomEnsemble.massSupport)
    (hmass1 : mass1 ∈ RandomEnsemble.massSupport)
    (hmass : mass0 ≠ mass1) :
    mass0 ∈ RandomEnsemble.massSupport ∧
      mass1 ∈ RandomEnsemble.massSupport ∧
      TwoPointProjectivePrerequisiteCertificate
        lambda mass0 mass1 := by
  exact ⟨hmass0, hmass1,
    twoPointProjectivePrerequisiteCertificate_of_distinct
      hlambda hmass⟩

#print axioms continuous_normalizedTransferDirection
#print axioms continuous_twoPointProjectiveMarkovOperator
#print axioms frozen_twoMass_projective_Feller_prerequisite_certificate

end

end ArchonPhysicsConsumers.Thermalization
