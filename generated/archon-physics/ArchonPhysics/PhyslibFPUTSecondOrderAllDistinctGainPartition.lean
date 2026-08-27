import ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
import ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

/-!
# Exact second-order formula with the all-distinct gain separated

This module substitutes the positive representative partition into the
original finite-volume second-order Haar identity.  The all-distinct A1 gain
is exposed as one summand; the positive mode-degenerate gain, cross-orbit
coherence, and the complete positive-inner matched feedback remain explicit.

No feedback reindex or kinetic approximation is used here.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctGainPartition

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Exact finite-volume broadening formula after separating the positive
all-distinct representative gain from its mode-degenerate complement. -/
theorem normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_allDistinctGain_add_remainders
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
      allDistinctRepresentativeA1GainSum
          m kappa time energy observed +
        positiveNonAllDistinctRepresentativeA1GainRemainder
          m kappa time energy observed +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re +
        ∑ term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed,
          compactIteratedQuadraticStaticFeedbackWeight m kappa
              (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
            finiteTimeResonanceWeight
              (iteratedQuadraticInnerMismatch m term.1) time := by
  rw [normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_gain_cross_explicitFeedback
    m kappa beta energy observed htime homega henergy]
  have hGain :=
    positiveRepresentativeA1GainSum_eq_allDistinct_add_nonAllDistinct
      m kappa time energy observed
  simp only [mul_assoc] at hGain
  rw [hGain]

end

end ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctGainPartition
