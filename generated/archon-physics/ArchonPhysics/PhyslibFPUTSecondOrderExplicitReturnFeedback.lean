import ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
import ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
import ArchonPhysics.PhyslibFPUTSecondOrderFiniteVolumeGainFeedbackDecomposition

/-!
# Explicit positive-frequency return feedback in the second-order formula

The finite-volume gain/feedback theorem retains one abstract real static
weight for every matched iterated tree.  Here that weight is replaced by its
fully expanded physical expression.  At a positive observed frequency, only
trees whose inner carrier also has positive frequency remain; every other
tree is zero by the original guards and tensor decoupling.

The index remains the original unquotiented matched-tree type, filtered only
by inner-frequency positivity.  Thus ordered outer slots, repeated modes,
all six return channels, and their original multiplicities are retained.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteVolumeGainFeedbackDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Matched return trees whose inner first-Picard carrier is a genuine
positive-frequency mode. -/
def positiveInnerMatchedIteratedQuadraticTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact Finset.univ.filter fun term ↦
    0 < modeFrequency m (iteratedQuadraticFirstPicardMode term.1)

/-- Compact signed physical prefactor for one positive-frequency return
tree.  The two interaction tensors are not identified with one another. -/
def compactIteratedQuadraticStaticFeedbackWeight
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  -firstPicardCoordinateBranchSign
      (iteratedQuadraticInnerEntry term).2 * kappa ^ 2 *
    interactionTensor m 3
      (Fin.cons observed (iteratedQuadraticOuterModes term)) *
    interactionTensor m 3
      (Fin.cons (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term).1.1) *
    radius observed * radius (iteratedQuadraticFreeMode term) *
    radius ((iteratedQuadraticInnerEntry term).1.1 0) *
    radius ((iteratedQuadraticInnerEntry term).1.1 1) /
    (32 * modeFrequency m (iteratedQuadraticFirstPicardMode term))

/-- On positive observed and inner carriers, the abstract broadening weight
is exactly the compact physical prefactor. -/
theorem iteratedQuadraticFeedbackStaticWeight_eq_compact_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term)) :
    iteratedQuadraticFeedbackStaticWeight m kappa radius observed term =
      compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term := by
  unfold iteratedQuadraticFeedbackStaticWeight
    compactIteratedQuadraticStaticFeedbackWeight
  exact re_freeInitial_mul_star_iteratedStaticCoefficient_eq_compact_of_pos
    m kappa radius observed term hObserved hInner

/-- At positive observed frequency, the full matched feedback sum is exactly
the inner-positive filtered sum of compact physical weights. -/
theorem matchedFeedbackBroadeningSum_eq_positiveInnerCompactSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    (∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
      iteratedQuadraticFeedbackStaticWeight m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) =
      ∑ term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed,
        compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time := by
  classical
  unfold positiveInnerMatchedIteratedQuadraticTerms
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro term hterm
  by_cases hInner :
      0 < modeFrequency m (iteratedQuadraticFirstPicardMode term.1)
  · rw [if_pos hInner,
      iteratedQuadraticFeedbackStaticWeight_eq_compact_of_pos
        m kappa radius observed term.1 hObserved hInner]
  · rw [if_neg hInner]
    have hzero :
        iteratedQuadraticFeedbackStaticWeight
          m kappa radius observed term.1 = 0 := by
      unfold iteratedQuadraticFeedbackStaticWeight
      rw [re_freeInitial_mul_star_iteratedStaticCoefficient_eq_guardedExpanded]
      simp [hObserved, hInner]
    rw [hzero]
    ring

/-- Exact finite-volume second-order formula with both gain and return
feedback written in physical collision variables.  Only the cross-orbit
coherent term remains opaque. -/
theorem normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_gain_cross_explicitFeedback
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
        ∑ term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed,
          compactIteratedQuadraticStaticFeedbackWeight m kappa
              (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
            finiteTimeResonanceWeight
              (iteratedQuadraticInnerMismatch m term.1) time := by
  rw [normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_gain_cross_feedback
      m kappa beta energy observed htime homega henergy,
    matchedFeedbackBroadeningSum_eq_positiveInnerCompactSum
      m kappa time (phaseEnergyRadius energy (modeFrequency m)) observed
      homega]

end

end ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
