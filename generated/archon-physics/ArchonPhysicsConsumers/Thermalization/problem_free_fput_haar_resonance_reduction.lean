import ArchonPhysics.FreeFPUTHaarResonanceReduction

/-!
# Consumer: free FPUT Haar resonance reduction

These finite-volume contracts record the extra rigidity of the freely
evaluated quadratic FPUT source: equal phase charge forces equal frequency
mismatch.  Consequently every surviving same-charge ordered pair in the
normalized first-Picard Haar second moment uses the ordinary finite-time
resonance weight.  The coherent off-diagonal pairs are retained, and the
perturbative coupling is exposed as one global squared-norm factor.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTHaarResonanceReduction

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTHaarResonanceReduction
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Equal quadratic phase charge fixes the free FPUT frequency mismatch. -/
theorem equal_charge_implies_equal_mismatch_contract
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    {left right : QuadraticPhaseTerm N}
    (hcharge : quadraticPhaseCharge left = quadraticPhaseCharge right) :
    quadraticPhaseMismatch frequency observed left =
      quadraticPhaseMismatch frequency observed right :=
  quadraticPhaseMismatch_eq_of_charge_eq frequency observed hcharge

/-- The normalized Haar first-Picard second moment is the full ordered-pair
sum over equal charges, with the ordinary finite-time resonance weight. -/
theorem normalized_firstPicard_secondMoment_sameCharge_contract
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
        else 0 :=
  normalized_integral_normSq_freeQuadraticCorrection_eq_sameChargePairSum
    coupling m observed radius frequency htime

/-- The same exact normalized moment exposes `Complex.normSq coupling` as a
single global factor without discarding any same-charge cross term. -/
theorem normalized_firstPicard_secondMoment_couplingSq_contract
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
          else 0 :=
  normalized_integral_normSq_freeQuadraticCorrection_eq_couplingSq_mul
    coupling m observed radius frequency htime

#print axioms equal_charge_implies_equal_mismatch_contract
#print axioms normalized_firstPicard_secondMoment_sameCharge_contract
#print axioms normalized_firstPicard_secondMoment_couplingSq_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTHaarResonanceReduction
