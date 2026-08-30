import ArchonPhysics.RandomMassTwoPointProjectiveLogGrowth

/-!
# Consumer: the two-point Furstenberg stationary-integral interface

For two distinct masses chosen from the frozen interval `[4/5, 6/5]` and a
positive spectral parameter, this consumer combines the previously
constructed stationary projective law with the algebraic Furstenberg
hypotheses and the integrable logarithmic norm cocycle.

The conclusion is a stationary-integral certificate for the equal-weight
two-atom transfer law.  It is not a Furstenberg positivity theorem and does
not assert a positive Lyapunov exponent, EFC, localization, or a conclusion
for the full continuous uniform mass law.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassTwoPointProjectiveLogGrowth
open ArchonPhysics.RandomMassTwoPointProjectiveMarkov
open ArchonPhysics.RandomMassTwoPointProjectiveStationary
open MeasureTheory

noncomputable section

/-- Any two distinct atoms in the frozen mass support have a stationary law
carrying the complete no-axiom Furstenberg integral certificate. -/
theorem frozen_twoMass_exists_FurstenbergIntegralCertificate
    {lambda mass0 mass1 : Real} (hlambda : 0 < lambda)
    (hmass0 : mass0 ∈ RandomEnsemble.massSupport)
    (hmass1 : mass1 ∈ RandomEnsemble.massSupport)
    (hmass : mass0 ≠ mass1) :
    mass0 ∈ RandomEnsemble.massSupport ∧
      mass1 ∈ RandomEnsemble.massSupport ∧
      ∃ law : ProbabilityMeasure OrientedProjectiveDirection,
        TwoPointFurstenbergIntegralCertificate
          lambda mass0 mass1 law := by
  refine ⟨hmass0, hmass1, ?_⟩
  obtain ⟨law, hstationary⟩ :=
    exists_twoPointProjectiveStationary lambda mass0 mass1
  exact ⟨law,
    twoPointFurstenbergIntegralCertificate_of_stationary
      hlambda hmass hstationary⟩

/-- In particular, the two endpoints `4/5` and `6/5` of the frozen support
give a concrete two-atom certificate. -/
theorem frozen_endpointMasses_exist_FurstenbergIntegralCertificate
    {lambda : Real} (hlambda : 0 < lambda) :
    ∃ law : ProbabilityMeasure OrientedProjectiveDirection,
      TwoPointFurstenbergIntegralCertificate
        lambda RandomEnsemble.massLower RandomEnsemble.massUpper law := by
  have hlower : RandomEnsemble.massLower ∈
      RandomEnsemble.massSupport := by
    simp [RandomEnsemble.massSupport, RandomEnsemble.massLower,
      RandomEnsemble.massUpper]
    norm_num
  have hupper : RandomEnsemble.massUpper ∈
      RandomEnsemble.massSupport := by
    simp [RandomEnsemble.massSupport, RandomEnsemble.massLower,
      RandomEnsemble.massUpper]
    norm_num
  have hdistinct : RandomEnsemble.massLower ≠
      RandomEnsemble.massUpper := by
    norm_num [RandomEnsemble.massLower, RandomEnsemble.massUpper]
  exact (frozen_twoMass_exists_FurstenbergIntegralCertificate
    hlambda hlower hupper hdistinct).2.2

#print axioms continuous_transferLogNormCocycle
#print axioms twoPointFurstenbergIntegralCertificate_of_stationary
#print axioms frozen_endpointMasses_exist_FurstenbergIntegralCertificate

end

end ArchonPhysicsConsumers.Thermalization
