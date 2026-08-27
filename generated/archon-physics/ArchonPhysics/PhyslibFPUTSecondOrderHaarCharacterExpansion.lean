import ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
import ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
import ArchonPhysics.FreeFPUTA0A1ChargeSeparation

/-!
# Exact second-order Haar character expansion for the Physlib FPUT coefficients

At a positive-frequency observed mode, the canonical free amplitude `A0`, the
microscopic quadratic first-Picard coefficient `A1`, and the complete
second-Picard coefficient `A2` are all exact finite initial-phase character
families.  This module inserts those three physical families into the generic
finite Haar identities.

The first-order `A0`/`A1` interference vanishes by exact charge separation.  At
second order, every same-charge `A1` term is retained inside its coherent fiber
norm square, and the complete `A2` fiber at the unique `A0` charge is retained
inside the initial/second-Picard interference.  These are fixed finite-volume,
finite-time identities; no collision operator or kinetic limit is asserted.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
open ArchonPhysics.FreeFPUTA0A1ChargeSeparation
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Deterministic coefficient of one character in the microscopic quadratic
first-Picard amplitude family. -/
def physlibQuadraticFirstPicardCharacterCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) : QuadraticPhaseTerm N → Complex :=
  oscillatoryCoefficient
    (freeQuadraticDuhamelCoefficient
      (physlibQuadraticCoupling m kappa 1 observed)
      m observed radius)
    (quadraticPhaseMismatch (modeFrequency m) observed) time

/-- The microscopic quadratic first-Picard amplitude is exactly the finite
character family with the coefficient defined above. -/
theorem physlibQuadraticFirstPicardCoefficient_eq_characterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time observed =
      finitePhaseCorrection
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed)
        quadraticPhaseCharge phase := by
  simpa [physlibQuadraticFirstPicardCharacterCoefficient] using
    physlibQuadraticFirstPicardCoefficient_eq_finitePhaseCorrection
      m kappa radius phase time observed

/-- At a positive-frequency observed mode, the physical canonical `A0` and
microscopic quadratic `A1` have exactly zero first-order Haar interference. -/
theorem integral_physlibFPUT_firstOrderInterference_eq_zero_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      secondMomentFirst
        (canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed)
      ∂finitePhaseHaarLaw (Lattice.Site N)) = 0 := by
  calc
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
        secondMomentFirst
          (finitePhaseCorrection
            (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
            (freeInitialPhaseCharge observed) phase)
          (finitePhaseCorrection
            (physlibQuadraticFirstPicardCharacterCoefficient
              m kappa radius time observed)
            quadraticPhaseCharge phase)
        ∂finitePhaseHaarLaw (Lattice.Site N) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        change secondMomentFirst
            (canonicalFreeComplexInitialAmplitude
              radius (modeFrequency m) phase observed)
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed) = _
        rw [canonicalFreeComplexInitialAmplitude_eq_phaseFamily_of_pos
          radius (modeFrequency m) phase observed homega,
          physlibQuadraticFirstPicardCoefficient_eq_characterFamily]
    _ = 0 :=
      integral_secondMomentFirst_freeInitial_quadratic_eq_zero observed
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed)

/-- Exact Haar average of the physical second-order coefficient.  The first
summand is the full coherent `A1` charge-fiber square; the second is the
interference with the complete `A2` fiber carrying the unique `A0` charge. -/
theorem integral_physlibFPUT_twoStepSecondCoefficient_eq_chargeFiber_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      twoStepSecondCoefficient
        (canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed)
        (physlibFPUTSecondPicardCoefficient
          m kappa beta observed radius phase time)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      sameChargeFiberNormSqSum
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int) +
        2 *
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
            starRingEnd Complex
              (coherentFiberCoefficient completeSecondPicardCharge
                (completeSecondPicardCoefficient
                  m kappa beta radius observed time)
                (freeInitialPhaseCharge observed 0))).re := by
  calc
    _ = ∫ phase : UnitAddTorus (Lattice.Site N),
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
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun phase ↦ by
        change twoStepSecondCoefficient
            (canonicalFreeComplexInitialAmplitude
              radius (modeFrequency m) phase observed)
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed)
            (physlibFPUTSecondPicardCoefficient
              m kappa beta observed radius phase time) = _
        rw [canonicalFreeComplexInitialAmplitude_eq_phaseFamily_of_pos
          radius (modeFrequency m) phase observed homega,
          physlibQuadraticFirstPicardCoefficient_eq_characterFamily,
          physlibFPUTSecondPicardCoefficient_eq_completeCharacterFamily]
    _ = _ :=
      integral_twoStepSecondCoefficient_finOne_eq_chargeFiber
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed)
        (quadraticPhaseCharge :
          QuadraticPhaseTerm N → Lattice.Site N → Int)
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        (completeSecondPicardCharge :
          CompleteSecondPicardCharacterTerm N → Lattice.Site N → Int)

/-- Haar-averaged harmonic modal-energy coefficient at order `g^2`: multiply
the complete second-moment coefficient by the observed mode frequency. -/
theorem integral_physlibFPUT_modalEnergySecondCoefficient_eq_chargeFiber_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      modeFrequency m observed *
        twoStepSecondCoefficient
          (canonicalFreeComplexInitialAmplitude
            radius (modeFrequency m) phase observed)
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      modeFrequency m observed *
        (sameChargeFiberNormSqSum
            (physlibQuadraticFirstPicardCharacterCoefficient
              m kappa radius time observed)
            (quadraticPhaseCharge :
              QuadraticPhaseTerm N → Lattice.Site N → Int) +
          2 *
            (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
              starRingEnd Complex
                (coherentFiberCoefficient completeSecondPicardCharge
                  (completeSecondPicardCoefficient
                    m kappa beta radius observed time)
                  (freeInitialPhaseCharge observed 0))).re) := by
  rw [integral_const_mul,
    integral_physlibFPUT_twoStepSecondCoefficient_eq_chargeFiber_of_pos
      m kappa beta radius time observed homega]

end

end ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
