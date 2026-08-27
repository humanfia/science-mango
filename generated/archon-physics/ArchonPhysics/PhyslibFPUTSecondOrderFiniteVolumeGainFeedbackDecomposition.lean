import ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

/-!
# Exact finite-volume gain/feedback decomposition at second order

This module inserts the canonical A1 collision-gain reindexing into the exact
second-order Picard/Haar broadening identity.  The result has three terms:

* the positive-frequency finite-time collision-kernel gain, with exact
  swap-orbit multiplicities;
* the real part of the cross-orbit coherent remainder;
* the complete charge-matched iterated return-tree feedback.

Nothing is hidden in a kinetic closure.  In particular, the last two terms
remain explicit and no repeated-mode multiplicity is identified with the
standard collision flux at this stage.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderFiniteVolumeGainFeedbackDecomposition

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Real form of the exact coherent A1 gain decomposition. -/
theorem real_physlibQuadraticFirstPicardBroadeningSum_eq_kernelSum_add_crossRe
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    (∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        Complex.normSq
          (physlibQuadraticFirstPicardStaticFiberCoefficient m kappa
            (phaseEnergyRadius energy (modeFrequency m)) observed charge) *
          finiteTimeResonanceWeight
            (outputChargeMismatch
              (modeFrequency m observed) charge (modeFrequency m)) time) =
      (∑ representative ∈
          positiveQuadraticSwapOrbitRepresentatives N m observed,
        ((quadraticSwapOrbit representative).card : Real) ^ 2 *
          (finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign representative) time
              (quadraticCollisionModes observed representative) *
            ∏ r : Fin 2,
              modeAction energy (modeFrequency m)
                (representative.1 r))) +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re := by
  have hcomplex := congrArg Complex.re
    (physlibQuadraticFirstPicardBroadeningSum_eq_kernelSum_add_cross
      m kappa time observed energy henergy)
  have hcard (card : Nat) :
      (((card : Complex) ^ 2).re) = (card : Real) ^ 2 := by
    norm_cast
  simpa [hcard] using hcomplex

/-- Exact positive-time order-`g^2` coefficient as finite-volume collision
gain, coherent cross-orbit correction, and the unquotiented return-tree
feedback sum. -/
theorem normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_gain_cross_feedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    (1 / time) *
      (∫ phase : UnitAddTorus (Lattice.Site N),
        twoStepSecondCoefficient
          (canonicalFreeComplexInitialAmplitude
            (phaseEnergyRadius energy (modeFrequency m))
            (modeFrequency m) phase observed)
          (physlibQuadraticFirstPicardCoefficient m kappa
            (phaseEnergyRadius energy (modeFrequency m)) phase time observed)
          (physlibFPUTSecondPicardCoefficient m kappa beta observed
            (phaseEnergyRadius energy (modeFrequency m)) phase time)
        ∂finitePhaseHaarLaw (Lattice.Site N)) =
      (∑ representative ∈
          positiveQuadraticSwapOrbitRepresentatives N m observed,
        ((quadraticSwapOrbit representative).card : Real) ^ 2 *
          (finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign representative) time
              (quadraticCollisionModes observed representative) *
            ∏ r : Fin 2,
              modeAction energy (modeFrequency m)
                (representative.1 r))) +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re +
        ∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
          iteratedQuadraticFeedbackStaticWeight m kappa
              (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
            finiteTimeResonanceWeight
              (iteratedQuadraticInnerMismatch m term.1) time := by
  rw [normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_broadeningSums_of_pos
      m kappa beta (phaseEnergyRadius energy (modeFrequency m)) observed
      htime homega,
    real_physlibQuadraticFirstPicardBroadeningSum_eq_kernelSum_add_crossRe
      m kappa time observed energy henergy]

end

end ArchonPhysics.PhyslibFPUTSecondOrderFiniteVolumeGainFeedbackDecomposition
