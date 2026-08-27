import ArchonPhysics.FreeFPUTDirectCubicA0InterferenceCancellation
import ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion

/-!
# Removal of the direct cubic branch from the second-order energy feedback

The complete second-Picard character family is a disjoint union of the
iterated-quadratic and direct-cubic branches.  At the unique charge carried
by the canonical free amplitude, the complete coherent fiber therefore
splits into those two coherent fibers.  The direct-cubic part has zero real
interference by the exact on-shell/pure-imaginary cancellation, leaving only
the iterated-quadratic return trees in the order-`g^2` energy feedback.

All identities are finite-volume and finite-time.  They do not identify the
remaining tree sum with a kinetic collision operator.
-/

namespace ArchonPhysics.PhyslibFPUTDirectCubicSecondOrderCancellation

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTDirectCubicA0InterferenceCancellation
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The coherent fiber of the complete sum-type family is the sum of the
coherent fibers of its two branches. -/
theorem coherentFiberCoefficient_completeSecondPicard_eq_add
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (charge : Lattice.Site N → Int) :
    coherentFiberCoefficient completeSecondPicardCharge
        (completeSecondPicardCoefficient
          m kappa beta radius observed time) charge =
      coherentFiberCoefficient iteratedQuadraticSecondPicardCharge
          (iteratedQuadraticSecondPicardNestedCoefficient
            m kappa radius observed time) charge +
        coherentFiberCoefficient cubicPhaseCharge
          (oscillatoryCoefficient
            (cubicDuhamelCoefficient
              (physicalCubicUnitCoupling (modeFrequency m observed) beta)
              m observed radius)
            (cubicPhaseMismatch (modeFrequency m) observed) time) charge := by
  classical
  unfold coherentFiberCoefficient
  rw [Fintype.sum_sum_type]
  rfl

/-- In coherent-fiber form, the charge-matched direct cubic branch has zero
real interference with the canonical free amplitude. -/
theorem two_mul_re_freeInitial_mul_star_directCubicFiber_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    2 *
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (coherentFiberCoefficient cubicPhaseCharge
            (oscillatoryCoefficient
              (cubicDuhamelCoefficient
                (physicalCubicUnitCoupling (modeFrequency m observed) beta)
                m observed radius)
              (cubicPhaseMismatch (modeFrequency m) observed) time)
            (freeInitialPhaseCharge observed 0))).re = 0 := by
  have hcancel :=
    equalChargeFamilyInterference_freeInitial_directCubic_eq_zero
      m beta time radius (modeFrequency m) observed
  unfold equalChargeFamilyInterference at hcancel
  rw [equalChargeCrossPairSum_finOne_left] at hcancel
  exact hcancel

/-- The complete A0/A2 feedback equals its iterated-quadratic part; the
direct cubic branch contributes no real second-order energy interference. -/
theorem completeSecondPicardFeedback_eq_iteratedQuadraticFeedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    2 *
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (coherentFiberCoefficient completeSecondPicardCharge
            (completeSecondPicardCoefficient
              m kappa beta radius observed time)
            (freeInitialPhaseCharge observed 0))).re =
      2 *
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
          starRingEnd Complex
            (coherentFiberCoefficient iteratedQuadraticSecondPicardCharge
              (iteratedQuadraticSecondPicardNestedCoefficient
                m kappa radius observed time)
              (freeInitialPhaseCharge observed 0))).re := by
  rw [coherentFiberCoefficient_completeSecondPicard_eq_add]
  calc
    2 *
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
          starRingEnd Complex
            (coherentFiberCoefficient iteratedQuadraticSecondPicardCharge
                (iteratedQuadraticSecondPicardNestedCoefficient
                  m kappa radius observed time)
                (freeInitialPhaseCharge observed 0) +
              coherentFiberCoefficient cubicPhaseCharge
                (oscillatoryCoefficient
                  (cubicDuhamelCoefficient
                    (physicalCubicUnitCoupling
                      (modeFrequency m observed) beta)
                    m observed radius)
                  (cubicPhaseMismatch (modeFrequency m) observed) time)
                (freeInitialPhaseCharge observed 0))).re =
      2 *
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
            starRingEnd Complex
              (coherentFiberCoefficient iteratedQuadraticSecondPicardCharge
                (iteratedQuadraticSecondPicardNestedCoefficient
                  m kappa radius observed time)
                (freeInitialPhaseCharge observed 0))).re +
        2 *
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
            starRingEnd Complex
              (coherentFiberCoefficient cubicPhaseCharge
                (oscillatoryCoefficient
                  (cubicDuhamelCoefficient
                    (physicalCubicUnitCoupling
                      (modeFrequency m observed) beta)
                    m observed radius)
                  (cubicPhaseMismatch (modeFrequency m) observed) time)
                (freeInitialPhaseCharge observed 0))).re := by
        simp only [map_add, mul_add, Complex.add_re]
    _ = _ := by
      rw [two_mul_re_freeInitial_mul_star_directCubicFiber_eq_zero, add_zero]

/-- Exact Haar order-`g^2` coefficient after the direct-cubic cancellation.
Only the coherent A1 square and iterated-quadratic return feedback remain. -/
theorem integral_physlibFPUT_twoStepSecondCoefficient_eq_iteratedFiber_of_pos
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
              (coherentFiberCoefficient iteratedQuadraticSecondPicardCharge
                (iteratedQuadraticSecondPicardNestedCoefficient
                  m kappa radius observed time)
                (freeInitialPhaseCharge observed 0))).re := by
  rw [integral_physlibFPUT_twoStepSecondCoefficient_eq_chargeFiber_of_pos
      m kappa beta radius time observed homega,
    completeSecondPicardFeedback_eq_iteratedQuadraticFeedback]

/-- Modal-energy version of the same exact cancellation. -/
theorem integral_physlibFPUT_modalEnergySecondCoefficient_eq_iteratedFiber_of_pos
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
                  (freeInitialPhaseCharge observed 0))).re) := by
  rw [integral_const_mul,
    integral_physlibFPUT_twoStepSecondCoefficient_eq_iteratedFiber_of_pos
      m kappa beta radius time observed homega]

end

end ArchonPhysics.PhyslibFPUTDirectCubicSecondOrderCancellation
