import ArchonPhysics.R32CanonicalDuhamelForceBridgeV3
import ArchonPhysics.R32WeightedModalErrorParseval

/-!
# Canonical modal readback of the R32 error energy

This small adapter states the exact Parseval identity directly for the
canonical actual and zero-coupling global trajectories.  It is an observable
readback only; it adds no dynamic or probabilistic premise.
-/

namespace ArchonPhysics.R32CanonicalModalErrorReadbackV1

open ArchonPhysics
open ArchonPhysics.R32CanonicalDuhamelForceBridgeV3
open ArchonPhysics.R32CanonicalExactFreeBridgeV3
open ArchonPhysics.R32ModalEnergyL1Stability
open ArchonPhysics.R32WeightedModalErrorParseval
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic

noncomputable section

variable {N : Nat} [NeZero N]

/-- Ordered frequency-weighted phase vector of the canonical global flow. -/
def canonicalWeightedOrderedHarmonicPhaseVector
    (kappa beta coupling : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) (time : Real) :
    OrderedModeIndex N → Complex :=
  weightedOrderedHarmonicPhaseVector
    (canonicalMass (N := N) omega)
    (canonicalMassWeightedPositionPath (N := N)
      kappa beta coupling hbeta a omega time)
    (canonicalMassWeightedMomentumPath (N := N)
      kappa beta coupling hbeta a omega time)

/-- Exact coefficient-one identity: the canonical Duhamel error energy is
the complete ordered-modal phase-space distance. -/
theorem canonicalWeightedModalDistance_eq_canonicalErrorEnergy
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    phaseSpaceL2Distance
        (canonicalWeightedOrderedHarmonicPhaseVector (N := N)
          kappa beta g hbeta a omega time)
        (canonicalWeightedOrderedHarmonicPhaseVector (N := N)
          kappa beta 0 hbeta a omega time) =
      canonicalErrorEnergy (N := N)
        kappa beta g hbeta a omega time := by
  simpa [canonicalWeightedOrderedHarmonicPhaseVector,
    canonicalExactFreePositionError, canonicalExactFreeMomentumError,
    canonicalErrorEnergy, harmonicOperatorCLM] using
    (phaseSpaceL2Distance_weighted_eq_harmonicEnergySeminorm
      (canonicalMass (N := N) omega) hsimple
      (canonicalMassWeightedPositionPath (N := N)
        kappa beta g hbeta a omega time)
      (canonicalMassWeightedMomentumPath (N := N)
        kappa beta g hbeta a omega time)
      (canonicalMassWeightedPositionPath (N := N)
        kappa beta 0 hbeta a omega time)
      (canonicalMassWeightedMomentumPath (N := N)
        kappa beta 0 hbeta a omega time))

#print axioms canonicalWeightedModalDistance_eq_canonicalErrorEnergy

end

end ArchonPhysics.R32CanonicalModalErrorReadbackV1
