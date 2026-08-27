import ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge

/-!
# Consumer: free FPUT energy/collision-weight bridge

These contracts expose the exact normalization of one signed quadratic FPUT
term initialized with `phaseEnergyRadius`.  Input energies are nonnegative,
and the observed/input triple satisfies `PositiveModeTuple`, so every
frequency used as a physical denominator is strictly positive.

Both statements are termwise.  They do not replace the coherent square of a
same-charge Haar fiber by a diagonal sum of term weights, and they make no
nonlinear, kinetic-limit, or thermalization claim.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTEnergyCollisionWeightBridge

open ArchonPhysics
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling

noncomputable section

/-- Before normalizing the observed complex mode, the squared raw coefficient
contains the explicit factor `2 * omega_observed`. -/
theorem raw_phaseEnergyRadius_coefficient_normSq_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (term : QuadraticPhaseTerm N)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    Complex.normSq
        (quadraticPhaseCoefficient m observed
          (phaseEnergyRadius energy (modeFrequency m)) term) =
      (2 * modeFrequency m observed) *
        normalizedInteractionWeight m
          (quadraticCollisionModes observed term) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r) :=
  normSq_quadraticPhaseCoefficient_phaseEnergyRadius_eq
    m observed energy term henergy hpositive

/-- With the physical output-mode coupling, the remaining prefactor is
exactly `(kappa * g)^2`; the other factors are the normalized interaction
weight and the two prescribed input actions. -/
theorem physical_coupling_coefficient_normSq_contract
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (term : QuadraticPhaseTerm N)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) term) =
      (kappa * g) ^ 2 *
        normalizedInteractionWeight m
          (quadraticCollisionModes observed term) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r) :=
  normSq_physicalQuadraticDuhamelCoefficient_eq
    kappa g m observed energy term henergy hpositive

#print axioms raw_phaseEnergyRadius_coefficient_normSq_contract
#print axioms physical_coupling_coefficient_normSq_contract

end


end ArchonPhysicsConsumers.Thermalization.FreeFPUTEnergyCollisionWeightBridge
