import ArchonPhysics.PhyslibFPUTSecondOrderReturnTreeFormula

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondOrderReturnTreeFormula
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer endpoint for the exact finite-volume second-order return-tree
formula. -/
theorem problem_physlibFPUT_twoStepSecondCoefficient_eq_returnTreeFormula
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
        ∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
          iteratedQuadraticFeedbackNormSqTerm
            m kappa time radius observed term.1 :=
  integral_physlibFPUT_twoStepSecondCoefficient_eq_returnTreeFormula_of_pos
    m kappa beta radius time observed homega

/-- Consumer endpoint for the corresponding harmonic modal-energy
coefficient. -/
theorem problem_physlibFPUT_modalEnergySecondCoefficient_eq_returnTreeFormula
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
          ∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
            iteratedQuadraticFeedbackNormSqTerm
              m kappa time radius observed term.1) :=
  integral_physlibFPUT_modalEnergySecondCoefficient_eq_returnTreeFormula_of_pos
    m kappa beta radius time observed homega

#print axioms
  problem_physlibFPUT_twoStepSecondCoefficient_eq_returnTreeFormula
#print axioms
  problem_physlibFPUT_modalEnergySecondCoefficient_eq_returnTreeFormula

end

end ArchonPhysicsConsumers.Thermalization
