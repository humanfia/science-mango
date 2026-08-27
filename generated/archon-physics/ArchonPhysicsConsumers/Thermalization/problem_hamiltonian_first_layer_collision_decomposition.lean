import ArchonPhysics.HamiltonianFirstLayerCollisionDecomposition

/-!
# Consumer: Hamiltonian first-layer collision decomposition

This consumer exposes the exact finite-volume bridge from the freely
evaluated quadratic Hamiltonian force to its coherent phase-charge fibers
and to the positive diagonal collision sum with an explicit off-diagonal
coherent remainder.
-/

namespace ArchonPhysicsConsumers.Thermalization.HamiltonianFirstLayerCollisionDecomposition

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
open ArchonPhysics.HamiltonianFirstLayerBroadening
open ArchonPhysics.HamiltonianFirstLayerCollisionDecomposition
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer endpoint retaining the complete coherent charge-fiber square. -/
theorem problem_physicalHamiltonianFirstLayer_eq_coherentChargeFiberSum
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
  exact
    normalized_integral_normSq_physicalHamiltonianFirstLayer_eq_chargeFiberSum
      kappa g m observed radius htime

/-- Consumer endpoint: the Hamiltonian first layer equals the physical
positive collision sum plus the full same-charge coherent remainder. -/
theorem problem_physicalHamiltonianFirstLayer_eq_collisionSum_add_coherent
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
  exact
    normalized_integral_normSq_physicalHamiltonianFirstLayer_eq_collisionSum_add_coherent
      kappa g m observed energy htime henergy

/-- Consumer endpoint equating the complete coherent fiber sum directly
with the positive collision sum and the retained coherent remainder. -/
theorem problem_physicalChargeFiberSum_eq_collisionSum_add_coherent
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
  exact physical_chargeFiberSum_eq_collisionSum_add_coherentRemainder
    kappa g m observed energy htime henergy

#print axioms problem_physicalHamiltonianFirstLayer_eq_coherentChargeFiberSum
#print axioms problem_physicalHamiltonianFirstLayer_eq_collisionSum_add_coherent
#print axioms problem_physicalChargeFiberSum_eq_collisionSum_add_coherent

end

end ArchonPhysicsConsumers.Thermalization.HamiltonianFirstLayerCollisionDecomposition
