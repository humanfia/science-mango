import ArchonPhysics.FreeFPUTAllDistinctRepresentativeA1Bridge

/-!
# Exact representative-level second-order closure

This module combines the original coherent first-Picard Haar sum with the
nested connected-return feedback over the positive all-distinct canonical
representatives.  That entire main sector is replaced exactly by the signed
three-wave collision sum.  The non-admissible representative and cross-orbit
coherent contributions remain visible as additive remainders.

The connected feedback here is still the nested sum of local eight-tree
images.  Identifying it with the corresponding filtered part of the original
matched-tree feedback requires the separate global connected-fiber
surjectivity theorem.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctRepresentativeSecondOrderClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeA1Bridge
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

noncomputable section

/-- Exact closure of the admissible representative A1 gain and its nested
connected feedback into the signed collision operator, while retaining every
other coherent A1 contribution. -/
theorem fullA1_add_allDistinctRepresentativeFeedback_eq_signedFlux_add_remainders
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    freeQuadraticFullSameChargePairSum
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time +
        (allDistinctRepresentativeConnectedFeedbackSum
          m kappa time energy observed : Complex) =
      (allDistinctRepresentativeSignedFluxSum
          m kappa time energy observed : Complex) +
        nonAdmissibleQuadraticRepresentativeGainRemainder
          m kappa time energy observed +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time := by
  rw [freeQuadraticFullSameChargePairSum_eq_admissible_add_remainders
    m kappa time energy observed hEnergy]
  have hClosure :=
    allDistinctRepresentativeGain_add_feedback_eq_signedFluxSum
      m kappa time energy observed hEnergy
  have hClosureComplex :=
    congrArg (fun x : Real ↦ (x : Complex)) hClosure
  push_cast at hClosureComplex
  calc
    _ = ((allDistinctRepresentativeA1GainSum
            m kappa time energy observed : Complex) +
          (allDistinctRepresentativeConnectedFeedbackSum
            m kappa time energy observed : Complex)) +
        nonAdmissibleQuadraticRepresentativeGainRemainder
          m kappa time energy observed +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time := by ring
    _ = _ := by rw [hClosureComplex]

end

end ArchonPhysics.FreeFPUTAllDistinctRepresentativeSecondOrderClosure
