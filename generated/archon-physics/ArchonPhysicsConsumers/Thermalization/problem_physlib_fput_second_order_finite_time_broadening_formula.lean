import ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

/-!
# Consumer: finite-time FPUT second-order broadening formula

This consumer exposes the exact positive-time normalization of the
Hamiltonian/Picard second-order coefficient.  Its finite resonance weights
are not replaced by limiting delta measures.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer endpoint for the exact norm-square/broadening conversion. -/
theorem problem_normSq_oscillatoryIntegral_eq_time_mul_resonanceWeight
    (mismatch : Real) {time : Real} (htime : 0 < time) :
    Complex.normSq
        (NonresonantOscillatoryGain.oscillatoryIntegral mismatch time) =
      time * finiteTimeResonanceWeight mismatch time :=
  normSq_oscillatoryIntegral_eq_time_mul_finiteTimeResonanceWeight
    mismatch htime

/-- Consumer endpoint for the normalized finite-volume second-order
broadening formula. -/
theorem problem_normalized_physlibFPUT_secondOrder_eq_broadeningSums
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed) :
    (1 / time) *
      (∫ phase : UnitAddTorus (Lattice.Site N),
        twoStepSecondCoefficient
          (canonicalFreeComplexInitialAmplitude
            radius (modeFrequency m) phase observed)
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase time)
        ∂finitePhaseHaarLaw (Lattice.Site N)) =
      (∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        Complex.normSq
            (physlibQuadraticFirstPicardStaticFiberCoefficient
              m kappa radius observed charge) *
          finiteTimeResonanceWeight
            (outputChargeMismatch
              (modeFrequency m observed) charge (modeFrequency m)) time) +
        ∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
          iteratedQuadraticFeedbackStaticWeight
              m kappa radius observed term.1 *
            finiteTimeResonanceWeight
              (iteratedQuadraticInnerMismatch m term.1) time :=
  normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_broadeningSums_of_pos
    m kappa beta radius observed htime homega

#print axioms
  problem_normSq_oscillatoryIntegral_eq_time_mul_resonanceWeight
#print axioms
  problem_normalized_physlibFPUT_secondOrder_eq_broadeningSums

end

end ArchonPhysicsConsumers.Thermalization
