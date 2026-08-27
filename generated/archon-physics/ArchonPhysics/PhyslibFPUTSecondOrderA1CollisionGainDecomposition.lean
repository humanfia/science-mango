import ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge
import ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
import ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder
import ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

/-!
# Exact collision-kernel decomposition of the second-order A1 gain

The coherent first-Picard square in the exact second-order broadening formula
is first reindexed by input-swap orbits.  Every positive-frequency canonical
representative is then identified with the existing microscopic finite-time
collision kernel times its two input actions.  Representatives containing a
zero-frequency leg vanish at the Hamiltonian vertex, while coherent pairs in
different swap orbits remain as an explicit remainder.

The resulting formula is an exact finite-volume identity.  In particular,
it does not discard the zero-charge cross-orbit remainder or identify the
return-tree feedback with a kinetic loss term.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

noncomputable section

/-- Canonical swap-orbit representatives whose observed and two input modes
all have strictly positive harmonic frequency. -/
def positiveQuadraticSwapOrbitRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (quadraticSwapOrbitRepresentatives N).filter fun term ↦
    PositiveModeTuple m (quadraticCollisionModes observed term)

/-- The real orbit base of one positive-frequency representative is exactly
the microscopic finite-time collision kernel times its two input actions. -/
theorem physicalQuadraticOrbitBase_eq_collisionKernel_mul_actions
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    (Complex.normSq
        (freeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) term) : Complex) *
        (finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed term) time :
            Complex) =
      ((finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign term) time
          (quadraticCollisionModes observed term) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r) : Real) : Complex) := by
  simpa [freeQuadraticSameChargePairValue, Complex.mul_conj] using
    (physicalQuadraticSameTermPairValue_eq_collisionKernel_mul_actions
      m kappa time observed energy term henergy hpositive)

/-- The complete canonical intra-orbit A1 contribution is a positive-mode
sum of card-squared collision kernels.  The nonpositive representatives are
proved zero through the interaction tensor, not by cancelling a zero
frequency denominator. -/
theorem physical_freeQuadraticSwapRepresentativeCollisionSum_eq_kernelSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    freeQuadraticSwapRepresentativeCollisionSum
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time =
      ∑ representative ∈
          positiveQuadraticSwapOrbitRepresentatives N m observed,
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          ((finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign representative) time
              (quadraticCollisionModes observed representative) *
            ∏ r : Fin 2,
              modeAction energy (modeFrequency m)
                (representative.1 r) : Real) : Complex) := by
  classical
  rw [freeQuadraticSwapRepresentativeCollisionSum_eq_cardSqSum]
  unfold positiveQuadraticSwapOrbitRepresentatives
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro representative hrepresentative
  by_cases hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed representative)
  · rw [if_pos hpositive]
    rw [show
      ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
            (Complex.normSq
              (freeQuadraticDuhamelCoefficient
                (physlibQuadraticCoupling m kappa 1 observed) m observed
                (phaseEnergyRadius energy (modeFrequency m))
                representative) : Complex) *
          (finiteTimeResonanceWeight
            (quadraticPhaseMismatch (modeFrequency m) observed
              representative) time : Complex) =
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          ((Complex.normSq
            (freeQuadraticDuhamelCoefficient
              (physlibQuadraticCoupling m kappa 1 observed) m observed
              (phaseEnergyRadius energy (modeFrequency m))
              representative) : Complex) *
            (finiteTimeResonanceWeight
              (quadraticPhaseMismatch (modeFrequency m) observed
                representative) time : Complex)) by ring,
      physicalQuadraticOrbitBase_eq_collisionKernel_mul_actions
        m kappa time observed energy representative
          (fun r ↦ henergy _) hpositive]
  · rw [if_neg hpositive,
      freeQuadraticDuhamelCoefficient_eq_zero_of_not_positive
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) representative hpositive]
    simp

/-- Exact full same-charge A1 gain: positive canonical collision kernels
with their correct orbit multiplicities, plus the unchanged cross-orbit
coherent remainder. -/
theorem physical_freeQuadraticFullSameChargePairSum_eq_kernelSum_add_cross
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    freeQuadraticFullSameChargePairSum
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time =
      (∑ representative ∈
          positiveQuadraticSwapOrbitRepresentatives N m observed,
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          ((finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign representative) time
              (quadraticCollisionModes observed representative) *
            ∏ r : Fin 2,
              modeAction energy (modeFrequency m)
                (representative.1 r) : Real) : Complex)) +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time := by
  rw [freeQuadraticFullSameChargePairSum_eq_intraOrbit_add_crossOrbit,
    freeQuadraticSwapIntraOrbitCollisionSum_eq_representativeSum,
    physical_freeQuadraticSwapRepresentativeCollisionSum_eq_kernelSum
      m kappa time observed energy henergy]

/-- The coherent charge-fiber broadening sum used in the second-order formula
is exactly the full same-charge ordered-pair sum. -/
theorem physlibQuadraticFirstPicardBroadeningSum_eq_fullSameChargePairSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        (Complex.normSq
          (physlibQuadraticFirstPicardStaticFiberCoefficient
            m kappa radius observed charge) : Complex) *
          (finiteTimeResonanceWeight
            (outputChargeMismatch
              (modeFrequency m observed) charge (modeFrequency m)) time :
                Complex)) =
      freeQuadraticFullSameChargePairSum
        (physlibQuadraticCoupling m kappa 1 observed) m observed radius
        (modeFrequency m) time := by
  symm
  simpa only [physlibQuadraticFirstPicardStaticFiberCoefficient,
    freeQuadraticChargeFiberCoefficient,
    freeQuadraticFullSameChargePairSum,
    freeQuadraticSameChargePairValue,
    quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
    outputChargeMismatch] using
    (sameChargePairSum_eq_realizedChargeFiberNormSqSum
      (charge := (quadraticPhaseCharge :
        QuadraticPhaseTerm N → Lattice.Site N → Int))
      (coefficient := freeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling m kappa 1 observed) m observed radius)
      (kernel := fun charge ↦
        (finiteTimeResonanceWeight
          (outputChargeMismatch
            (modeFrequency m observed) charge (modeFrequency m)) time :
              Complex)))

/-- Final A1 gain identity in the variables of the exact second-order
broadening theorem. -/
theorem physlibQuadraticFirstPicardBroadeningSum_eq_kernelSum_add_cross
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    (∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        (Complex.normSq
          (physlibQuadraticFirstPicardStaticFiberCoefficient m kappa
            (phaseEnergyRadius energy (modeFrequency m)) observed charge) :
              Complex) *
          (finiteTimeResonanceWeight
            (outputChargeMismatch
              (modeFrequency m observed) charge (modeFrequency m)) time :
                Complex)) =
      (∑ representative ∈
          positiveQuadraticSwapOrbitRepresentatives N m observed,
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          ((finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign representative) time
              (quadraticCollisionModes observed representative) *
            ∏ r : Fin 2,
              modeAction energy (modeFrequency m)
                (representative.1 r) : Real) : Complex)) +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time := by
  rw [physlibQuadraticFirstPicardBroadeningSum_eq_fullSameChargePairSum,
    physical_freeQuadraticFullSameChargePairSum_eq_kernelSum_add_cross
      m kappa time observed energy henergy]

end

end ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
