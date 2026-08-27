import ArchonPhysics.FiniteModalEnergyProbabilityTransfer

/-!
# Consumer: probability transfer from modal state to modal energy
-/

namespace ArchonPhysicsConsumers.Thermalization.FiniteModalEnergyProbabilityTransfer

open Filter MeasureTheory Topology
open ArchonPhysics
open ArchonPhysics.FiniteModalEnergyProbabilityTransfer
open ArchonPhysics.ThermalizationTransfer

noncomputable section

/-- An `O(g)` modal RMS comparison on a high-probability event implies
convergence in probability of the normalized modal-energy profile. -/
theorem problem_normalizedEnergy_convergesInProbability
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (size : Nat → Nat) (coupling : Nat → Real)
    (a b : (j : Nat) → Omega → Fin (size j + 1) → E)
    (amplitudeCeilingA amplitudeCeilingB errorCoefficient
      energyDensityFloor : Real)
    (certificate : ModalStateGoodEventCertificate probability size coupling
      a b amplitudeCeilingA amplitudeCeilingB errorCoefficient)
    (energyData : NormalizedEnergyGoodEventData size a b
      certificate.goodEvent energyDensityFloor)
    (hcoupling : Tendsto coupling atTop (nhds 0)) :
    ConvergesInProbabilityTo probability
      (fun j omega ↦ ENNReal.ofReal
        (indexedNormalizedEnergyError size a b j omega)) 0 := by
  exact normalizedEnergy_convergesInProbability probability size coupling
    a b amplitudeCeilingA amplitudeCeilingB errorCoefficient
      energyDensityFloor certificate energyData hcoupling

#print axioms problem_normalizedEnergy_convergesInProbability
#print axioms ModalStateGoodEventCertificate.perModeEnergy_convergesInProbability
#print axioms normalizedEnergy_convergesInProbability

end

end ArchonPhysicsConsumers.Thermalization.FiniteModalEnergyProbabilityTransfer
