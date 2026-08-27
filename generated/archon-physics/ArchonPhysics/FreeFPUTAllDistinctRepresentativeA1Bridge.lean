import ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
import ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge

/-!
# Physical A1 gain split at all-distinct representatives

The exact Haar first-Picard contribution is already grouped into canonical
input-swap orbits.  This module identifies every positive all-distinct orbit
summand with the real collision-kernel gain used by the local gain--loss
identity, and retains every other representative in an explicit remainder.

Together with the pre-existing cross-orbit coherent remainder, this gives an
exact bridge from the original complex Haar formula to the admissible A1 gain
sum.  No positivity or distinctness is imposed on the retained remainder.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctRepresentativeA1Bridge

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticCollisionKernelBridge
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

noncomputable section

/-- Canonical representatives outside the positive all-distinct sector retain
their exact original coherent orbit contribution. -/
def nonAdmissibleQuadraticRepresentativeGainRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Complex := by
  classical
  exact
    ∑ q ∈ (quadraticSwapOrbitRepresentatives N).filter
        (fun q ↦ ¬ (ObservedQuadraticAllDistinct observed q ∧
          PositiveModeTuple m (quadraticCollisionModes observed q))),
      freeQuadraticSwapOrbitContribution
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time q

/-- On one admissible representative, the exact coherent swap-orbit
contribution is the complex embedding of the local real A1 gain. -/
theorem physicalQuadraticSwapOrbitContribution_eq_localA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    freeQuadraticSwapOrbitContribution
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time q =
      (allDistinctLocalA1Gain m kappa time energy observed q : Complex) := by
  rw [freeQuadraticSwapOrbitContribution_eq_card_sq_mul]
  unfold allDistinctLocalA1Gain
  have hDiagonal :=
    physicalQuadraticDiagonalTerm_eq_finiteTimeCollisionKernel_mul_actions
      m kappa time observed energy q (fun r ↦ hEnergy (q.1 r)) hPositive
  have hDiagonalComplex :=
    congrArg (fun x : Real ↦ (x : Complex)) hDiagonal
  calc
    _ = ((quadraticSwapOrbit q).card : Complex) ^ 2 *
        ((Complex.normSq
            (freeQuadraticDuhamelCoefficient
              (physlibQuadraticCoupling m kappa 1 observed) m observed
              (phaseEnergyRadius energy (modeFrequency m)) q) *
          finiteTimeResonanceWeight
            (quadraticPhaseMismatch (modeFrequency m) observed q) time :
              Real) : Complex) := by
          push_cast
          ring
    _ = ((quadraticSwapOrbit q).card : Complex) ^ 2 *
        ((finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          ∏ r : Fin 2,
            modeAction energy (modeFrequency m) (q.1 r) : Real) : Complex) := by
          rw [hDiagonalComplex]
    _ = _ := by
          push_cast
          ring

/-- Exact split of the no-double-counted representative A1 sum into the
positive all-distinct collision gains and an explicit complementary
remainder. -/
theorem freeQuadraticSwapRepresentativeCollisionSum_eq_admissible_add_remainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    freeQuadraticSwapRepresentativeCollisionSum
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time =
      (allDistinctRepresentativeA1GainSum
          m kappa time energy observed : Complex) +
        nonAdmissibleQuadraticRepresentativeGainRemainder
          m kappa time energy observed := by
  classical
  unfold freeQuadraticSwapRepresentativeCollisionSum
    allDistinctRepresentativeA1GainSum
    positiveAllDistinctQuadraticSwapRepresentatives
    nonAdmissibleQuadraticRepresentativeGainRemainder
  rw [← Finset.sum_filter_add_sum_filter_not
    (quadraticSwapOrbitRepresentatives N)
    (fun q ↦ ObservedQuadraticAllDistinct observed q ∧
      PositiveModeTuple m (quadraticCollisionModes observed q))]
  congr 1
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  have hconditions := (Finset.mem_filter.mp hq).2
  exact physicalQuadraticSwapOrbitContribution_eq_localA1Gain
    m kappa time energy observed q hEnergy hconditions.2

/-- The original full coherent A1 Haar sum is the admissible collision gain,
the non-admissible representative remainder, and the unchanged cross-orbit
coherent remainder. -/
theorem freeQuadraticFullSameChargePairSum_eq_admissible_add_remainders
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    freeQuadraticFullSameChargePairSum
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time =
      (allDistinctRepresentativeA1GainSum
          m kappa time energy observed : Complex) +
        nonAdmissibleQuadraticRepresentativeGainRemainder
          m kappa time energy observed +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time := by
  rw [freeQuadraticFullSameChargePairSum_eq_representativeCardSq_add_cross]
  rw [← freeQuadraticSwapRepresentativeCollisionSum_eq_cardSqSum]
  rw [freeQuadraticSwapRepresentativeCollisionSum_eq_admissible_add_remainder
    m kappa time energy observed hEnergy]

end

end ArchonPhysics.FreeFPUTAllDistinctRepresentativeA1Bridge
