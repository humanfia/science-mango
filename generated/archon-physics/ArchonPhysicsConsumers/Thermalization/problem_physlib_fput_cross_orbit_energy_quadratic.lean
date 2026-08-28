import ArchonPhysics.PhyslibFPUTCrossOrbitEnergyQuadratic

/-!
# Consumer: cross-orbit energy quadratic representation

This consumer checks the exact conversion of the exceptional coherent
cross-orbit term into a finite quadratic polynomial on nonnegative modal
energy profiles.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCrossOrbitEnergyQuadratic

open ArchonPhysics
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure
open ArchonPhysics.PhyslibFPUTCrossOrbitEnergyQuadratic
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

open scoped ComplexConjugate

noncomputable section

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m) (site : Lattice.Site N) :
    extendPositiveEnergyProfile m energy site =
      modeFrequency m site *
        modeAction (extendPositiveEnergyProfile m energy)
          (modeFrequency m) site :=
  extendPositiveEnergyProfile_eq_frequency_mul_modeAction m energy site

example {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (time : Real) :
    IsPositiveEnergyQuadratic m
      (zeroChargeCrossOrbitEnergyPolynomial coupling m observed time) :=
  isPositiveEnergyQuadratic_zeroChargeCrossOrbitEnergyPolynomial
    coupling m observed time

example {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : PositiveEnergyProfile m)
    (time : Real) (henergy : ∀ mode, 0 ≤ energy mode) :
    (freeQuadraticCrossSwapOrbitCoherentRemainder coupling m observed
        (phaseEnergyRadius (extendPositiveEnergyProfile m energy)
          (modeFrequency m))
        (modeFrequency m) time).re =
      zeroChargeCrossOrbitEnergyPolynomial
        coupling m observed time energy :=
  freeQuadraticCrossSwapOrbitCoherentRemainder_re_eq_energyPolynomial
    coupling m observed energy time henergy

#print axioms isPositiveEnergyQuadratic_extendedEnergyProduct
#print axioms isPositiveEnergyQuadratic_zeroChargeCrossOrbitEnergyPolynomial
#print axioms
  freeQuadraticCrossSwapOrbitCoherentRemainder_re_eq_energyPolynomial

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCrossOrbitEnergyQuadratic
