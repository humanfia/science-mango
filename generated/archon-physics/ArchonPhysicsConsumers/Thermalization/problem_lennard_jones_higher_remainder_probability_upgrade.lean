import ArchonPhysics.LennardJonesHigherRemainderProbabilityUpgrade

/-!
# Consumer: project probability law for the higher LJ remainder
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesHigherRemainderProbabilityUpgrade

open Filter MeasureTheory Topology
open ArchonPhysics
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.LennardJonesStoppedHigherRemainderProbability
open ArchonPhysics.LennardJonesHigherRemainderProbabilityUpgrade

noncomputable section

/-- The explicit stopped-flow certificate now has the exact bundled
convergence-in-probability type consumed by the F3 reduction. -/
theorem problem_higherRemainder_convergesInProbabilityTo_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (coupling : Nat → Real) (coefficient : Real)
    (error : Nat → Omega → Real)
    (certificate : VanishingGoodEventRemainderCertificate
      probability coupling coefficient error)
    (hcoupling : Tendsto coupling atTop (nhds 0)) :
    ConvergesInProbabilityTo probability (ennrealError error) 0 := by
  exact convergesInProbabilityTo_zero_of_certificate
    probability coupling coefficient error certificate hcoupling

#print axioms problem_higherRemainder_convergesInProbabilityTo_zero
#print axioms localUniformError_zero_law_of_certificate
#print axioms convergesInProbabilityTo_zero_of_certificate

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesHigherRemainderProbabilityUpgrade
