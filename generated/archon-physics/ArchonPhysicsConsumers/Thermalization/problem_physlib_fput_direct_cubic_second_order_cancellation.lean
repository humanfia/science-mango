import ArchonPhysics.PhyslibFPUTDirectCubicSecondOrderCancellation

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTDirectCubicSecondOrderCancellation
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

theorem problem_completeSecondPicardFeedback_eq_iteratedQuadraticFeedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    2 *
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (coherentFiberCoefficient
            completeSecondPicardCharge
            (completeSecondPicardCoefficient
              m kappa beta radius observed time)
            (freeInitialPhaseCharge observed 0))).re =
      2 *
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
          starRingEnd Complex
            (coherentFiberCoefficient iteratedQuadraticSecondPicardCharge
              (iteratedQuadraticSecondPicardNestedCoefficient
                m kappa radius observed time)
              (freeInitialPhaseCharge observed 0))).re :=
  completeSecondPicardFeedback_eq_iteratedQuadraticFeedback
    m kappa beta radius observed time

theorem problem_physlibFPUT_modalEnergySecondCoefficient_eq_iteratedFiber
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
                (coherentFiberCoefficient iteratedQuadraticSecondPicardCharge
                  (iteratedQuadraticSecondPicardNestedCoefficient
                    m kappa radius observed time)
                  (freeInitialPhaseCharge observed 0))).re) :=
  integral_physlibFPUT_modalEnergySecondCoefficient_eq_iteratedFiber_of_pos
    m kappa beta radius time observed homega

#print axioms
  problem_completeSecondPicardFeedback_eq_iteratedQuadraticFeedback
#print axioms
  problem_physlibFPUT_modalEnergySecondCoefficient_eq_iteratedFiber

end

end ArchonPhysicsConsumers.Thermalization
