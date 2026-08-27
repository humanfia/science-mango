import ArchonPhysics.FiniteTimeResonanceWeight
import ArchonPhysics.PhyslibFPUTSecondOrderReturnTreeFormula

/-!
# Finite-time broadening form of the second-order FPUT coefficient

For a positive observation time, every one-step oscillatory norm square is
exactly the observation time times `finiteTimeResonanceWeight`.  Applying
this identity to both parts of the exact return-tree formula gives a
time-normalized finite-volume coefficient with two explicit finite sums:

* coherent first-Picard charge-fiber broadening;
* charge-matched iterated return-tree broadening.

No large-time delta limit, thermodynamic limit, or kinetic closure is used.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondOrderReturnTreeFormula
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Positive-time conversion between the division-free norm square and the
finite-time resonance weight. -/
theorem normSq_oscillatoryIntegral_eq_time_mul_finiteTimeResonanceWeight
    (mismatch : Real) {time : Real} (htime : 0 < time) :
    Complex.normSq (oscillatoryIntegral mismatch time) =
      time * finiteTimeResonanceWeight mismatch time := by
  rw [Complex.normSq_eq_norm_sq, finiteTimeResonanceWeight, if_pos htime]
  field_simp

/-- Before time integration, the coherent first-Picard coefficient in one
charge fiber. -/
def physlibQuadraticFirstPicardStaticFiberCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (charge : Lattice.Site N → Int) : Complex :=
  freeQuadraticChargeFiberCoefficient
    (physlibQuadraticCoupling m kappa 1 observed)
    m observed radius charge

/-- In a fixed charge fiber, every first-Picard term has the same mismatch,
so its common oscillatory integral factors out of the coherent sum. -/
theorem coherentFiberCoefficient_physlibFirstPicard_eq_static_mul_oscillatory
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (charge : Lattice.Site N → Int) :
    coherentFiberCoefficient quadraticPhaseCharge
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius time observed) charge =
      physlibQuadraticFirstPicardStaticFiberCoefficient
          m kappa radius observed charge *
        oscillatoryIntegral
          (outputChargeMismatch
            (modeFrequency m observed) charge (modeFrequency m)) time := by
  classical
  unfold coherentFiberCoefficient
    physlibQuadraticFirstPicardCharacterCoefficient
    physlibQuadraticFirstPicardStaticFiberCoefficient
    freeQuadraticChargeFiberCoefficient oscillatoryCoefficient
    quadraticPhaseMismatch
  unfold coherentFiberCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro term hterm
  by_cases hcharge : quadraticPhaseCharge term = charge
  · rw [if_pos hcharge, if_pos hcharge, hcharge]
  · rw [if_neg hcharge, if_neg hcharge]
    simp

/-- Static real weight of one charge-matched iterated return tree. -/
def iteratedQuadraticFeedbackStaticWeight
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
    starRingEnd Complex
      (iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term)).re

/-- Each return-tree feedback term is observation time times its broadened
static weight. -/
theorem iteratedQuadraticFeedbackNormSqTerm_eq_time_mul_broadening
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    {time : Real} (htime : 0 < time) :
    iteratedQuadraticFeedbackNormSqTerm
        m kappa time radius observed term =
      time *
        (iteratedQuadraticFeedbackStaticWeight
            m kappa radius observed term *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term) time) := by
  unfold iteratedQuadraticFeedbackNormSqTerm
    iteratedQuadraticFeedbackStaticWeight
  rw [normSq_oscillatoryIntegral_eq_time_mul_finiteTimeResonanceWeight
    (iteratedQuadraticInnerMismatch m term) htime]
  ring

/-- Positive-time normalization of the complete coherent A1 square. -/
theorem one_div_time_mul_sameChargeFiberNormSqSum_eq_broadeningSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time) :
    (1 / time) *
        sameChargeFiberNormSqSum
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int) =
      ∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        Complex.normSq
            (physlibQuadraticFirstPicardStaticFiberCoefficient
              m kappa radius observed charge) *
          finiteTimeResonanceWeight
            (outputChargeMismatch
              (modeFrequency m observed) charge (modeFrequency m)) time := by
  classical
  unfold sameChargeFiberNormSqSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro charge hcharge
  rw [coherentFiberCoefficient_physlibFirstPicard_eq_static_mul_oscillatory,
    Complex.normSq_mul,
    normSq_oscillatoryIntegral_eq_time_mul_finiteTimeResonanceWeight
      (outputChargeMismatch
        (modeFrequency m observed) charge (modeFrequency m)) htime]
  field_simp

/-- Positive-time normalization of the complete matched return-tree sum. -/
theorem one_div_time_mul_matchedFeedbackSum_eq_broadeningSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time) :
    (1 / time) *
        (∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
          iteratedQuadraticFeedbackNormSqTerm
            m kappa time radius observed term.1) =
      ∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
        iteratedQuadraticFeedbackStaticWeight
            m kappa radius observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  rw [iteratedQuadraticFeedbackNormSqTerm_eq_time_mul_broadening
    m kappa radius observed term.1 htime]
  field_simp

/-- Exact positive-time broadening formula for the normalized second-order
Haar coefficient. -/
theorem normalized_integral_physlibFPUT_twoStepSecondCoefficient_eq_broadeningSums_of_pos
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
              (iteratedQuadraticInnerMismatch m term.1) time := by
  rw [integral_physlibFPUT_twoStepSecondCoefficient_eq_returnTreeFormula_of_pos
      m kappa beta radius time observed homega,
    mul_add,
    one_div_time_mul_sameChargeFiberNormSqSum_eq_broadeningSum
      m kappa radius observed htime,
    one_div_time_mul_matchedFeedbackSum_eq_broadeningSum
      m kappa radius observed htime]

end

end ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula
