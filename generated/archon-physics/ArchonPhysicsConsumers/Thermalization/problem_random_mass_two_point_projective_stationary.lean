import ArchonPhysics.RandomMassTwoPointProjectiveStationary

/-!
# Consumer: a stationary two-point projective transfer law

For two distinct masses in the frozen support and a positive spectral
parameter, this consumer combines the algebraic/Feller prerequisite
certificate with the stationary probability law constructed by empirical
Markov-orbit averages.

Stationarity is the only new probabilistic conclusion.  This file does not
invoke a Furstenberg positivity theorem and does not assert a positive
Lyapunov exponent, EFC, or localization.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassTwoPointProjectiveMarkov
open ArchonPhysics.RandomMassTwoPointProjectiveStationary
open MeasureTheory

noncomputable section

/-- Frozen-support certificate combining noncompact projective dynamics,
strong irreducibility, Feller continuity, and an actual stationary law. -/
theorem frozen_twoMass_projective_stationary_certificate
    {lambda mass0 mass1 : Real} (hlambda : 0 < lambda)
    (hmass0 : mass0 ∈ RandomEnsemble.massSupport)
    (hmass1 : mass1 ∈ RandomEnsemble.massSupport)
    (hmass : mass0 ≠ mass1) :
    mass0 ∈ RandomEnsemble.massSupport ∧
      mass1 ∈ RandomEnsemble.massSupport ∧
      ∃ law : ProbabilityMeasure OrientedProjectiveDirection,
        IsTwoPointProjectiveStationary lambda mass0 mass1 law ∧
          TwoPointProjectivePrerequisiteCertificate
            lambda mass0 mass1 := by
  refine ⟨hmass0, hmass1, ?_⟩
  obtain ⟨law, hlaw⟩ :=
    exists_twoPointProjectiveStationary lambda mass0 mass1
  exact ⟨law, hlaw,
    twoPointProjectivePrerequisiteCertificate_of_distinct
      hlambda hmass⟩

#print axioms integral_markov_cesaro_sub
#print axioms exists_twoPointProjectiveStationary
#print axioms frozen_twoMass_projective_stationary_certificate

end

end ArchonPhysicsConsumers.Thermalization
