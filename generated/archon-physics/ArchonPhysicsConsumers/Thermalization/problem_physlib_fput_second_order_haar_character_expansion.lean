import ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion

/-!
# Consumer: exact second-order Physlib FPUT Haar character expansion

This consumer exposes the exact finite-volume vanishing of the physical
first-order Haar interference, the complete second-order charge-fiber formula,
and its harmonic modal-energy multiple.  It makes no collision or kinetic-limit
claim.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer endpoint for exact first-order `A0`/`A1` Haar cancellation. -/
theorem problem_physlibFPUT_firstOrderInterference_eq_zero
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
      ∂finitePhaseHaarLaw (Lattice.Site N)) = 0 :=
  integral_physlibFPUT_firstOrderInterference_eq_zero_of_pos
    m kappa radius time observed homega

/-- Consumer endpoint for the complete physical second-order charge-fiber
identity. -/
theorem problem_physlibFPUT_twoStepSecondCoefficient_eq_chargeFiber
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
                (freeInitialPhaseCharge observed 0))).re :=
  integral_physlibFPUT_twoStepSecondCoefficient_eq_chargeFiber_of_pos
    m kappa beta radius time observed homega

/-- Consumer endpoint for the harmonic modal-energy order-`g^2` coefficient.
-/
theorem problem_physlibFPUT_modalEnergySecondCoefficient_eq_chargeFiber
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
                  (freeInitialPhaseCharge observed 0))).re) :=
  integral_physlibFPUT_modalEnergySecondCoefficient_eq_chargeFiber_of_pos
    m kappa beta radius time observed homega

#print axioms problem_physlibFPUT_firstOrderInterference_eq_zero
#print axioms problem_physlibFPUT_twoStepSecondCoefficient_eq_chargeFiber
#print axioms problem_physlibFPUT_modalEnergySecondCoefficient_eq_chargeFiber

end

end ArchonPhysicsConsumers.Thermalization
