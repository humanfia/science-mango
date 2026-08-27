import ArchonPhysics.FiniteHaarOscillatorySecondMoment

/-!
# Consumer: two-term finite Haar oscillatory second moment

This consumer fixes two Duhamel terms with the same phase charge.  Expanding
the exact Haar formula displays both off-diagonal cross terms, even when the
two terms have different frequency mismatches.  It also instantiates the
positive-time normalized formula and the diagonal interface to the existing
real finite-time resonance weight.
-/

namespace ArchonPhysicsConsumers.Thermalization.FiniteHaarOscillatorySecondMoment

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Both terms carry the same zero charge on a single phase coordinate. -/
def sharedTwoTermCharge : Fin 2 -> Fin 1 -> Int := fun _ _ => 0

/-- The two explicit term indices have identical charge vectors. -/
theorem sharedTwoTermCharge_equal (j k : Fin 2) :
    sharedTwoTermCharge j = sharedTwoTermCharge k := rfl

/-- With two same-charge terms the exact second moment contains all four
ordered pairs.  In particular the `0,1` and `1,0` off-diagonal factors are
present and keep their separate mismatches. -/
theorem twoTerm_sameCharge_crossPairs_contract
    (coefficient : Fin 2 -> Complex) (mismatch : Fin 2 -> Real) (T : Real) :
    (∫ phase : UnitAddTorus (Fin 1),
      (Complex.normSq
        (finiteHaarOscillatorySum coefficient sharedTwoTermCharge
          mismatch T phase) : Complex)
      ∂finitePhaseHaarLaw (Fin 1)) =
      (coefficient 0 * starRingEnd Complex (coefficient 0) *
          oscillatoryCrossProduct (mismatch 0) (mismatch 0) T +
        coefficient 0 * starRingEnd Complex (coefficient 1) *
          oscillatoryCrossProduct (mismatch 0) (mismatch 1) T) +
      (coefficient 1 * starRingEnd Complex (coefficient 0) *
          oscillatoryCrossProduct (mismatch 1) (mismatch 0) T +
        coefficient 1 * starRingEnd Complex (coefficient 1) *
          oscillatoryCrossProduct (mismatch 1) (mismatch 1) T) := by
  have h01 : sharedTwoTermCharge 0 = sharedTwoTermCharge 1 := rfl
  have h10 : sharedTwoTermCharge 1 = sharedTwoTermCharge 0 := rfl
  simpa only [Fin.sum_univ_two, if_pos h01, if_pos h10, if_true] using
    integral_normSq_finiteHaarOscillatorySum_eq_crossPairSum
      coefficient sharedTwoTermCharge mismatch T

/-- The positive-time normalized identity still contains the two distinct
off-diagonal cross-resonance weights. -/
theorem twoTerm_normalized_crossWeights_contract
    (coefficient : Fin 2 -> Complex) (mismatch : Fin 2 -> Real)
    {T : Real} (hT : 0 < T) :
    (1 / (T : Complex)) *
        (∫ phase : UnitAddTorus (Fin 1),
          (Complex.normSq
            (finiteHaarOscillatorySum coefficient sharedTwoTermCharge
              mismatch T phase) : Complex)
          ∂finitePhaseHaarLaw (Fin 1)) =
      (coefficient 0 * starRingEnd Complex (coefficient 0) *
          finiteTimeCrossResonanceWeight (mismatch 0) (mismatch 0) T +
        coefficient 0 * starRingEnd Complex (coefficient 1) *
          finiteTimeCrossResonanceWeight (mismatch 0) (mismatch 1) T) +
      (coefficient 1 * starRingEnd Complex (coefficient 0) *
          finiteTimeCrossResonanceWeight (mismatch 1) (mismatch 0) T +
        coefficient 1 * starRingEnd Complex (coefficient 1) *
          finiteTimeCrossResonanceWeight (mismatch 1) (mismatch 1) T) := by
  have h01 : sharedTwoTermCharge 0 = sharedTwoTermCharge 1 := rfl
  have h10 : sharedTwoTermCharge 1 = sharedTwoTermCharge 0 := rfl
  simpa only [Fin.sum_univ_two, if_pos h01, if_pos h10, if_true] using
    normalized_integral_normSq_eq_equalChargeCrossWeightSum
      coefficient sharedTwoTermCharge mismatch hT

/-- The explicitly selected first diagonal pair reduces to the existing real
finite-time resonance weight. -/
theorem firstDiagonal_finiteTimeResonanceWeight_contract
    (coefficient : Fin 2 -> Complex) (mismatch : Fin 2 -> Real) (T : Real) :
    coefficient 0 * starRingEnd Complex (coefficient 0) *
        finiteTimeCrossResonanceWeight (mismatch 0) (mismatch 0) T =
      ((Complex.normSq (coefficient 0) *
        finiteTimeResonanceWeight (mismatch 0) T : Real) : Complex) := by
  exact normalized_diagonal_pair_eq_finiteTimeResonanceWeight
    coefficient mismatch 0 T

#print axioms twoTerm_sameCharge_crossPairs_contract
#print axioms twoTerm_normalized_crossWeights_contract
#print axioms firstDiagonal_finiteTimeResonanceWeight_contract
#print axioms normalized_integral_normSq_eq_equalChargeCrossWeightSum
#print axioms finiteTimeCrossResonanceWeight_self

end

end ArchonPhysicsConsumers.Thermalization.FiniteHaarOscillatorySecondMoment
