import ArchonPhysics.FreeFPUTDuhamelResonanceBridge

/-!
# Consumer checks for the free FPUT Duhamel resonance bridge

These finite-volume contracts expose the exact Haar second moment of the free
first-Picard correction, its fixed-phase resonant/nonresonant decomposition,
and the deterministic inverse-mismatch estimate for the nonresonant sector.
They make no assertion about the true nonlinear Duhamel remainder or a
lattice-size-uniform resonance gap.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTDuhamelResonanceBridge

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteOscillatoryResonanceSplit
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Haar averaging retains every ordered pair of free Duhamel terms carrying
the same phase charge, including off-diagonal repeated-charge pairs. -/
theorem free_duhamel_haar_equal_charge_second_moment_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      (Complex.normSq
        (freeQuadraticInteractionPictureCorrection
          coupling m observed radius frequency time phase) : Complex)
      ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = quadraticPhaseCharge right then
          oscillatoryCoefficient
              (freeQuadraticDuhamelCoefficient coupling m observed radius)
              (quadraticPhaseMismatch frequency observed) time left *
            starRingEnd Complex
              (oscillatoryCoefficient
                (freeQuadraticDuhamelCoefficient coupling m observed radius)
                (quadraticPhaseMismatch frequency observed) time right)
        else 0 :=
  integral_normSq_freeQuadraticInteractionPictureCorrection_eq_equalChargePairSum
    coupling m observed radius frequency time

/-- Exact fixed-phase decomposition into secular zero-mismatch terms and the
remaining nonresonant oscillatory sum. -/
theorem free_duhamel_resonant_nonresonant_split_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticInteractionPictureCorrection
        coupling m observed radius frequency time phase =
      (∑ term ∈ resonantIndices Finset.univ
          (quadraticPhaseMismatch frequency observed),
        phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase term) * time +
        nonresonantOscillatorySum Finset.univ
          (phasedFreeQuadraticDuhamelCoefficient
            coupling m observed radius phase)
          (quadraticPhaseMismatch frequency observed) time :=
  freeQuadraticInteractionPictureCorrection_eq_resonantTime_add_nonresonant
    coupling m observed radius frequency time phase

/-- Every nonresonant term receives the exact deterministic inverse-mismatch
gain.  The estimate is uniform in time but not asserted uniform in `N`. -/
theorem free_duhamel_nonresonant_inverse_mismatch_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    ‖nonresonantOscillatorySum Finset.univ
        (phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase)
        (quadraticPhaseMismatch frequency observed) time‖ ≤
      2 * ∑ term ∈ nonresonantIndices Finset.univ
          (quadraticPhaseMismatch frequency observed),
        ‖phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase term‖ /
          |quadraticPhaseMismatch frequency observed term| :=
  norm_nonresonantFreeQuadraticInteractionPictureCorrection_le
    coupling m observed radius frequency time phase

/-- Phase-independent inverse-mismatch bound.  Unit norm of every Haar
character exposes the perturbative coupling as a single prefactor. -/
theorem free_duhamel_nonresonant_inverse_mismatch_coupling_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    ‖nonresonantOscillatorySum Finset.univ
        (phasedFreeQuadraticDuhamelCoefficient
          coupling m observed radius phase)
        (quadraticPhaseMismatch frequency observed) time‖ ≤
      2 * ‖coupling‖ *
        ∑ term ∈ nonresonantIndices Finset.univ
          (quadraticPhaseMismatch frequency observed),
          ‖quadraticPhaseCoefficient m observed radius term‖ /
            |quadraticPhaseMismatch frequency observed term| :=
  norm_nonresonantFreeQuadraticInteractionPictureCorrection_le_coupling
    coupling m observed radius frequency time phase

#check freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum
#check freeQuadraticInteractionPictureCorrection_eq_oscillatorySum_univ

#print axioms free_duhamel_haar_equal_charge_second_moment_contract
#print axioms free_duhamel_resonant_nonresonant_split_contract
#print axioms free_duhamel_nonresonant_inverse_mismatch_contract
#print axioms free_duhamel_nonresonant_inverse_mismatch_coupling_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTDuhamelResonanceBridge
