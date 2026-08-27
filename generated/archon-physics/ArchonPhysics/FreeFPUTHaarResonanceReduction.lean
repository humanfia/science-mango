import ArchonPhysics.FreeFPUTDuhamelResonanceBridge

/-!
# Free FPUT Haar resonance reduction

For a generic finite character expansion, equal phase charge need not imply
equal frequency mismatch.  The freely evaluated quadratic FPUT source is
more rigid: its mismatch is the observed frequency minus the frequency paired
with its phase charge.  Hence every equal-charge Haar pair has one common
finite-time resonance weight.

The surviving pairs are still coherent ordered pairs, not just diagonal
terms.  This module neither discards those cross terms nor identifies their
coherent coefficient with a nonlinear collision operator.  It is an exact
finite-volume first-Picard statement only.
-/

namespace ArchonPhysics.FreeFPUTHaarResonanceReduction

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- For the free quadratic FPUT expansion, equal phase charge forces equal
frequency mismatch. -/
theorem quadraticPhaseMismatch_eq_of_charge_eq
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    {left right : QuadraticPhaseTerm N}
    (hcharge : quadraticPhaseCharge left = quadraticPhaseCharge right) :
    quadraticPhaseMismatch frequency observed left =
      quadraticPhaseMismatch frequency observed right := by
  rw [quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
    quadraticPhaseMismatch_eq_output_sub_chargeFrequency, hcharge]

/-- The normalized Haar second moment of the free quadratic first-Picard
correction uses the ordinary real finite-time resonance weight on every
surviving same-charge ordered pair.  Distinct same-charge terms remain. -/
theorem normalized_integral_normSq_freeQuadraticCorrection_eq_sameChargePairSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) :
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (freeQuadraticInteractionPictureCorrection
              coupling m observed radius frequency time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = quadraticPhaseCharge right then
          freeQuadraticDuhamelCoefficient coupling m observed radius left *
            starRingEnd Complex
              (freeQuadraticDuhamelCoefficient
                coupling m observed radius right) *
            (finiteTimeResonanceWeight
              (quadraticPhaseMismatch frequency observed left) time : Complex)
        else 0 := by
  calc
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (freeQuadraticInteractionPictureCorrection
              coupling m observed radius frequency time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = quadraticPhaseCharge right then
          freeQuadraticDuhamelCoefficient coupling m observed radius left *
            starRingEnd Complex
              (freeQuadraticDuhamelCoefficient
                coupling m observed radius right) *
            finiteTimeCrossResonanceWeight
              (quadraticPhaseMismatch frequency observed left)
              (quadraticPhaseMismatch frequency observed right) time
        else 0 := by
      rw [show
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (freeQuadraticInteractionPictureCorrection
              coupling m observed radius frequency time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
          ∫ phase : UnitAddTorus (Lattice.Site N),
            (Complex.normSq
              (finiteHaarOscillatorySum
                (freeQuadraticDuhamelCoefficient coupling m observed radius)
                quadraticPhaseCharge
                (quadraticPhaseMismatch frequency observed) time phase) :
              Complex)
            ∂finitePhaseHaarLaw (Lattice.Site N) by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun phase => by
            change
              (Complex.normSq
                (freeQuadraticInteractionPictureCorrection
                  coupling m observed radius frequency time phase) : Complex) =
                (Complex.normSq
                  (finiteHaarOscillatorySum
                    (freeQuadraticDuhamelCoefficient
                      coupling m observed radius)
                    quadraticPhaseCharge
                    (quadraticPhaseMismatch frequency observed)
                    time phase) : Complex)
            rw [freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum]]
      exact normalized_integral_normSq_eq_equalChargeCrossWeightSum
        (freeQuadraticDuhamelCoefficient coupling m observed radius)
        (quadraticPhaseCharge :
          QuadraticPhaseTerm N → Lattice.Site N → Int)
        (quadraticPhaseMismatch frequency observed) htime
    _ = ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = quadraticPhaseCharge right then
          freeQuadraticDuhamelCoefficient coupling m observed radius left *
            starRingEnd Complex
              (freeQuadraticDuhamelCoefficient
                coupling m observed radius right) *
            (finiteTimeResonanceWeight
              (quadraticPhaseMismatch frequency observed left) time : Complex)
        else 0 := by
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      by_cases hcharge :
          quadraticPhaseCharge left = quadraticPhaseCharge right
      · rw [if_pos hcharge, if_pos hcharge,
          quadraticPhaseMismatch_eq_of_charge_eq
            frequency observed hcharge,
          finiteTimeCrossResonanceWeight_self]
      · rw [if_neg hcharge, if_neg hcharge]

/-- The preceding exact pair formula exposes the squared perturbative
coupling as one global prefactor. -/
theorem normalized_integral_normSq_freeQuadraticCorrection_eq_couplingSq_mul
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) :
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (freeQuadraticInteractionPictureCorrection
              coupling m observed radius frequency time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      (Complex.normSq coupling : Complex) *
        ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
          if quadraticPhaseCharge left = quadraticPhaseCharge right then
            quadraticPhaseCoefficient m observed radius left *
              starRingEnd Complex
                (quadraticPhaseCoefficient m observed radius right) *
              (finiteTimeResonanceWeight
                (quadraticPhaseMismatch frequency observed left) time : Complex)
          else 0 := by
  rw [normalized_integral_normSq_freeQuadraticCorrection_eq_sameChargePairSum
    coupling m observed radius frequency htime, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left hleft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right hright
  by_cases hcharge : quadraticPhaseCharge left = quadraticPhaseCharge right
  · rw [if_pos hcharge, if_pos hcharge]
    simp only [freeQuadraticDuhamelCoefficient, map_mul]
    rw [← Complex.mul_conj coupling]
    ring
  · rw [if_neg hcharge, if_neg hcharge]
    ring

end

end ArchonPhysics.FreeFPUTHaarResonanceReduction
