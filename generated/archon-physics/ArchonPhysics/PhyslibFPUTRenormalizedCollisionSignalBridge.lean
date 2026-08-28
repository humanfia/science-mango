import ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
import ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure

/-!
# Bridge from the renormalized actual drift to the finite-time collision signal

The signed coefficient subtracted from the actual Haar drift is identified
here with the existing normalized second-order FPUT broadening.  Consequently
the exact q-level signed-flux decomposition applies directly to the kinetic
signal extracted from the microscopic Hamiltonian flow.
-/

namespace ArchonPhysics.PhyslibFPUTRenormalizedCollisionSignalBridge

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The signed coefficient isolated from the genuine actual drift is exactly
the Haar integral of the physical two-step order-two coefficient. -/
theorem physlibHaarFiniteTimeKineticCoefficient_eq_integral
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    physlibHaarFiniteTimeKineticCoefficient
        m kappa beta radius time observed =
      ∫ phase : UnitAddTorus (Lattice.Site N),
        twoStepSecondCoefficient
          (canonicalFreeComplexInitialAmplitude
            radius (modeFrequency m) phase observed)
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time)
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
  unfold physlibHaarFiniteTimeKineticCoefficient
  calc
    finiteCharacterFamilySecondOrderCoefficient
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed)
        quadraticPhaseCharge
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge =
      ∫ phase : UnitAddTorus (Lattice.Site N),
        twoStepSecondCoefficient
          (finitePhaseCorrection
            (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
            (freeInitialPhaseCharge observed) phase)
          (finitePhaseCorrection
            (physlibQuadraticFirstPicardCharacterCoefficient
              m kappa radius time observed)
            quadraticPhaseCharge phase)
          (finitePhaseCorrection
            (completeSecondPicardCoefficient
              m kappa beta radius observed time)
            completeSecondPicardCharge phase)
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      exact (integral_twoStepSecondCoefficient_finitePhaseCorrections
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed)
        quadraticPhaseCharge
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        dsimp only
        rw [canonicalFreeComplexInitialAmplitude_eq_phaseFamily_of_pos
            radius (modeFrequency m) phase observed homega,
          physlibQuadraticFirstPicardCoefficient_eq_characterFamily,
          physlibFPUTSecondPicardCoefficient_eq_completeCharacterFamily]

/-- With the physical energy-radius parametrization, the normalized signed
coefficient is definitionally the existing finite-volume Haar broadening. -/
theorem normalized_physlibHaarFiniteTimeKineticCoefficient_eq_broadening
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (homega : 0 < modeFrequency m observed) :
    (1 / time) * physlibHaarFiniteTimeKineticCoefficient
        m kappa beta (phaseEnergyRadius energy (modeFrequency m))
          time observed =
      normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time := by
  unfold normalizedSecondOrderHaarBroadening
  rw [physlibHaarFiniteTimeKineticCoefficient_eq_integral
    m kappa beta (phaseEnergyRadius energy (modeFrequency m))
      time observed homega]

/-- The kinetic signal extracted from the actual one-block drift therefore
inherits the full exact q-level gain/feedback/remainder decomposition. -/
theorem normalized_physlibHaarFiniteTimeKineticCoefficient_eq_qLevelClosure
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    (1 / time) * physlibHaarFiniteTimeKineticCoefficient
        m kappa beta (phaseEnergyRadius energy (modeFrequency m))
          time observed =
      qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy observed +
        allEqualOrbitGainSum m kappa time energy observed +
        repeatedAwayFixedPointCorrection m kappa time energy observed +
        observedChildPlacementCorrection m kappa time energy observed +
        allEqualChannelFiveCorrection m kappa time energy observed +
        secondOrderCounterrotatingRemainder
          m kappa time energy observed +
        secondOrderCrossOrbitRemainder
          m kappa time energy observed := by
  calc
    _ = normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time :=
      normalized_physlibHaarFiniteTimeKineticCoefficient_eq_broadening
        m kappa beta energy observed time homega
    _ = _ := normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
      m kappa beta energy observed htime homega henergy

end

end ArchonPhysics.PhyslibFPUTRenormalizedCollisionSignalBridge
