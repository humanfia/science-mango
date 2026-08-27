import ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
import ArchonPhysics.PhyslibFPUTDirectCubicSecondOrderCancellation

/-!
# Exact return-tree formula for the second-order FPUT energy coefficient

The complete finite-volume second-order Haar coefficient can now be written
without an opaque `A2` fiber.  The direct cubic branch cancels from the real
`A0`/`A2` interference, while every charge-matched iterated-quadratic tree
has an outer mismatch equal to the negative of its inner mismatch.  Its
nested time integral therefore reduces to a one-step oscillatory norm square.

The resulting formula consists of the full coherent `A1` charge-fiber square
plus an unquotiented finite sum over all matched return trees.  Repeated modes,
both ordered outer slots, and both coordinate conjugation branches remain in
the index.  This is still a finite-time Picard identity, not yet a kinetic
gain-loss reindexing or a thermodynamic limit.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderReturnTreeFormula

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
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTDirectCubicSecondOrderCancellation
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The coherent iterated-A2 fiber interference is exactly the subtype sum
over all charge-matched return trees. -/
theorem two_mul_re_freeInitial_mul_star_iteratedFiber_eq_matchedSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    2 *
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (coherentFiberCoefficient iteratedQuadraticSecondPicardCharge
            (iteratedQuadraticSecondPicardNestedCoefficient
              m kappa radius observed time)
            (freeInitialPhaseCharge observed 0))).re =
      ∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
        iteratedQuadraticFeedbackNormSqTerm
          m kappa time radius observed term.1 := by
  have hmatched :=
    equalChargeFamilyInterference_freeInitial_completeInl_eq_matchedSum
      m kappa beta time radius observed
  unfold ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion.equalChargeFamilyInterference
    at hmatched
  rw [equalChargeCrossPairSum_finOne_left] at hmatched
  simpa only [completeSecondPicardCoefficient_inl,
    completeSecondPicardCharge_inl] using hmatched

/-- Complete exact Haar formula at perturbative order `g^2`: coherent A1
gain plus the finite charge-matched return-tree feedback sum. -/
theorem integral_physlibFPUT_twoStepSecondCoefficient_eq_returnTreeFormula_of_pos
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
            m kappa time radius observed term.1 := by
  rw [integral_physlibFPUT_twoStepSecondCoefficient_eq_iteratedFiber_of_pos
      m kappa beta radius time observed homega,
    two_mul_re_freeInitial_mul_star_iteratedFiber_eq_matchedSum
      m kappa beta time radius observed]

/-- Harmonic modal-energy form of the same exact return-tree formula. -/
theorem integral_physlibFPUT_modalEnergySecondCoefficient_eq_returnTreeFormula_of_pos
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
              m kappa time radius observed term.1) := by
  rw [integral_const_mul,
    integral_physlibFPUT_twoStepSecondCoefficient_eq_returnTreeFormula_of_pos
      m kappa beta radius time observed homega]

end

end ArchonPhysics.PhyslibFPUTSecondOrderReturnTreeFormula
