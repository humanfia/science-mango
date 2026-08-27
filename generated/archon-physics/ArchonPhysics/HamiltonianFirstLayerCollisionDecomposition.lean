import ArchonPhysics.HamiltonianFirstLayerBroadening
import ArchonPhysics.FreeFPUTChargeFiberAggregation
import ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder

/-!
# Hamiltonian first-layer collision decomposition

This module starts from the first interaction-picture Picard term defined as
the time integral of the freely evaluated quadratic Hamiltonian force.  Haar
averaging its squared norm gives two exact finite-volume descriptions:

* a sum of squared coherent coefficients over integer phase-charge fibers;
* the positive-frequency diagonal collision-weight sum plus the complete
  same-charge off-diagonal coherent remainder.

The charge-fiber square is not replaced by an incoherent termwise sum.  In
particular, equal-charge permutations and their interference factors remain
present.  The only discarded-looking sector is the nonpositive-frequency
diagonal, which is proved identically zero because every such interaction
tensor contains a zero-frequency bond mode.  No kinetic equation, RPA
closure, thermodynamic limit, or nonlinear remainder estimate is assumed.
-/

namespace ArchonPhysics.HamiltonianFirstLayerCollisionDecomposition

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder
open ArchonPhysics.HamiltonianFirstLayerBroadening
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The Haar second moment of the physical Hamiltonian first Picard layer is
exactly the coherent charge-fiber resonance sum.  Every same-charge
off-diagonal cross term is retained inside the norm square of its fiber. -/
theorem normalized_integral_normSq_physicalHamiltonianFirstLayer_eq_chargeFiberSum
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) :
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (physicalFreeQuadraticHamiltonianFirstLayer
              kappa g m observed radius time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        (Complex.normSq
          (freeQuadraticChargeFiberCoefficient
            (physicalQuadraticCoupling kappa g m observed)
            m observed radius charge) : Complex) *
          (finiteTimeResonanceWeight
            (outputChargeMismatch
              (modeFrequency m observed) charge (modeFrequency m)) time :
                Complex) := by
  simpa only [physicalFreeQuadraticHamiltonianFirstLayer_eq_correction] using
    (normalized_integral_normSq_freeQuadraticCorrection_eq_chargeFiberSum
      (physicalQuadraticCoupling kappa g m observed) m observed radius
      (modeFrequency m) htime)

/-- With nonnegative prescribed modal energies, the same Hamiltonian first
layer is exactly the positive three-leg collision-weight sum plus the full
same-charge off-diagonal coherent remainder.  The nonpositive diagonal has
been eliminated by its independently proved structural zero theorem. -/
theorem normalized_integral_normSq_physicalHamiltonianFirstLayer_eq_collisionSum_add_coherent
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) (henergy : ∀ mode, 0 ≤ energy mode) :
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (physicalFreeQuadraticHamiltonianFirstLayer
              kappa g m observed
              (phaseEnergyRadius energy (modeFrequency m)) time phase) :
                Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ((∑ term ∈ positiveQuadraticPhaseTerms m observed,
          (kappa * g) ^ 2 *
            normalizedInteractionWeight m
              (quadraticCollisionModes observed term) *
            (∏ r : Fin 2,
              modeAction energy (modeFrequency m) (term.1 r)) *
            finiteTimeResonanceWeight
              (quadraticPhaseMismatch
                (modeFrequency m) observed term) time : Real) : Complex) +
        freeQuadraticOffDiagonalCoherentRemainder
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) time := by
  simpa only [physicalFreeQuadraticHamiltonianFirstLayer_eq_correction,
    physical_nonpositiveFreeQuadraticDiagonalRemainder_eq_zero,
    Complex.ofReal_zero, add_zero] using
      (normalized_physical_freeQuadraticCorrection_eq_collisionSum_add_remainders
        kappa g m observed energy htime henergy)

/-- The coherent charge-fiber representation itself equals the physical
positive collision sum plus the exact same-charge off-diagonal remainder. -/
theorem physical_chargeFiberSum_eq_collisionSum_add_coherentRemainder
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) (henergy : ∀ mode, 0 ≤ energy mode) :
    (∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        (Complex.normSq
          (freeQuadraticChargeFiberCoefficient
            (physicalQuadraticCoupling kappa g m observed) m observed
            (phaseEnergyRadius energy (modeFrequency m)) charge) : Complex) *
          (finiteTimeResonanceWeight
            (outputChargeMismatch (modeFrequency m observed)
              charge (modeFrequency m)) time : Complex)) =
      ((∑ term ∈ positiveQuadraticPhaseTerms m observed,
          (kappa * g) ^ 2 *
            normalizedInteractionWeight m
              (quadraticCollisionModes observed term) *
            (∏ r : Fin 2,
              modeAction energy (modeFrequency m) (term.1 r)) *
            finiteTimeResonanceWeight
              (quadraticPhaseMismatch
                (modeFrequency m) observed term) time : Real) : Complex) +
        freeQuadraticOffDiagonalCoherentRemainder
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) time := by
  rw [← normalized_integral_normSq_physicalHamiltonianFirstLayer_eq_chargeFiberSum
    kappa g m observed (phaseEnergyRadius energy (modeFrequency m)) htime]
  exact
    normalized_integral_normSq_physicalHamiltonianFirstLayer_eq_collisionSum_add_coherent
      kappa g m observed energy htime henergy

end

end ArchonPhysics.HamiltonianFirstLayerCollisionDecomposition
