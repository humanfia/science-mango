import ArchonPhysics.PhyslibFPUTZeroChargeEnergyFactorization

/-!
# Consumer: zero-charge energy factorization

This consumer checks that a zero phase-charge quadratic Duhamel coefficient
is exactly a deterministic coefficient times one modal energy, including the
zero-frequency branch handled by the core theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTZeroChargeEnergyFactorization

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTZeroChargeEnergyFactorization

noncomputable section

example {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (hzero : quadraticPhaseCharge term = 0) :
    freeQuadraticDuhamelCoefficient coupling m observed
        (phaseEnergyRadius energy (modeFrequency m)) term =
      zeroChargeDuhamelEnergyCoefficient coupling m observed term *
        energy (term.1 0) :=
  freeQuadraticDuhamelCoefficient_phaseEnergyRadius_eq_energy
    coupling m observed energy term henergy hzero

#print axioms zeroChargeDuhamelEnergyCoefficient
#print axioms freeQuadraticDuhamelCoefficient_phaseEnergyRadius_eq_energy

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTZeroChargeEnergyFactorization
