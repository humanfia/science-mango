import ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition

/-!
# Consumer: free FPUT diagonal collision decomposition

These contracts expose the exact finite same-charge diagonal/off-diagonal
split and its physical free-FPUT specialization.  In the latter, only the
strictly positive-frequency diagonal sector is rewritten as normalized
collision weights.  The nonpositive-frequency diagonal and coherent
same-charge off-diagonal sectors remain explicit remainders.

Nothing here cancels either remainder or asserts a nonlinear gain-loss
equation, kinetic limit, or thermalization theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTDiagonalCollisionDecomposition

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Every finite same-charge ordered-pair sum is exactly its literal diagonal
plus the complete distinct same-charge ordered-pair remainder. -/
theorem same_charge_pair_sum_diagonal_offDiagonal_contract
    {J Q : Type*} [Fintype J]
    (charge : J → Q) (pairValue : J → J → Complex) :
    sameChargeOrderedPairSum charge pairValue =
      (∑ term, pairValue term term) +
        offDiagonalSameChargeRemainder charge pairValue :=
  sameChargeOrderedPairSum_eq_diagonal_add_offDiagonal charge pairValue

/-- For physical coupling and nonnegative prescribed input energies, the
positive-frequency diagonal is the normalized collision-weight sum.  The
nonpositive diagonal and coherent off-diagonal contributions are retained. -/
theorem physical_firstPicard_secondMoment_threeSector_contract
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) (henergy : ∀ mode, 0 ≤ energy mode) :
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (freeQuadraticInteractionPictureCorrection
              (physicalQuadraticCoupling kappa g m observed) m observed
              (phaseEnergyRadius energy (modeFrequency m))
              (modeFrequency m) time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ((∑ term ∈ positiveQuadraticPhaseTerms m observed,
          (kappa * g) ^ 2 *
            normalizedInteractionWeight m
              (quadraticCollisionModes observed term) *
            (∏ r : Fin 2,
              modeAction energy (modeFrequency m) (term.1 r)) *
            finiteTimeResonanceWeight
              (quadraticPhaseMismatch (modeFrequency m) observed term) time :
          Real) : Complex) +
        (nonpositiveFreeQuadraticDiagonalRemainder
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) time : Complex) +
        freeQuadraticOffDiagonalCoherentRemainder
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) time :=
  normalized_physical_freeQuadraticCorrection_eq_collisionSum_add_remainders
    kappa g m observed energy htime henergy

#print axioms same_charge_pair_sum_diagonal_offDiagonal_contract
#print axioms physical_firstPicard_secondMoment_threeSector_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTDiagonalCollisionDecomposition
