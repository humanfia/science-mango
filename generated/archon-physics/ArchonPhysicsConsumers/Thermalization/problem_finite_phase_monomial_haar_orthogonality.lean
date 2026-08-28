import ArchonPhysics.FinitePhaseMonomialHaarOrthogonality

/-!
# Consumer: exact finite RPA/Haar monomial orthogonality

This consumer instantiates the generic result with two explicit monomials on
one Haar phase coordinate: the empty monomial and one positive phase factor.
Their exponent signatures are distinct, so their cross term vanishes and the
second moment of their finite sum is exactly diagonal, both initially and
after deterministic free harmonic propagation.
-/

namespace ArchonPhysicsConsumers.Thermalization.FinitePhaseMonomialHaarOrthogonality

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FinitePhaseMonomialHaarOrthogonality
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Empty monomial versus one positive phase factor on a single mode. -/
def twoDistinctMonomials :
    Fin 2 → List (SignedMode (Fin 1))
  | 0 => []
  | 1 => [⟨0, .phase⟩]

/-- The two concrete monomials have different integer signatures. -/
theorem twoDistinctMonomials_signature_ne :
    phaseSignature (twoDistinctMonomials 0) ≠
      phaseSignature (twoDistinctMonomials 1) := by
  intro hequal
  have hcoordinate := congrFun hequal 0
  norm_num [twoDistinctMonomials, phaseSignature, monomialCharge,
    SignedMode.charge, PhaseSign.exponent, Pi.single_apply] at hcoordinate

/-- The complete signature map of the two-term family is injective. -/
theorem twoDistinctMonomials_signature_injective :
    Function.Injective
      (fun j : Fin 2 ↦ phaseSignature (twoDistinctMonomials j)) := by
  intro j k hsignature
  fin_cases j <;> fin_cases k
  · rfl
  · exact False.elim (twoDistinctMonomials_signature_ne hsignature)
  · exact False.elim
      (twoDistinctMonomials_signature_ne hsignature.symm)
  · rfl

/-- The explicit off-diagonal cross term vanishes exactly under Haar phase
averaging. -/
theorem twoDistinctMonomials_cross_eq_zero_contract
    (leftCoefficient rightCoefficient : Complex) :
    (∫ phase : UnitAddTorus (Fin 1),
      weightedMonomialCross leftCoefficient rightCoefficient
        (twoDistinctMonomials 0) (twoDistinctMonomials 1) phase
      ∂finitePhaseHaarLaw (Fin 1)) = 0 := by
  exact integral_weightedMonomialCross_eq_zero_of_signature_ne
    leftCoefficient rightCoefficient
    (twoDistinctMonomials 0) (twoDistinctMonomials 1)
    twoDistinctMonomials_signature_ne

/-- The expected squared norm of the explicit two-term family is the sum of
the two coefficient norm squares. -/
theorem twoDistinctMonomials_diagonalSecondMoment_contract
    (coefficient : Fin 2 → Complex) :
    (∫ phase : UnitAddTorus (Fin 1),
      Complex.normSq
        (finiteWeightedMonomialFamily coefficient twoDistinctMonomials phase)
      ∂finitePhaseHaarLaw (Fin 1)) =
      ∑ j, Complex.normSq (coefficient j) := by
  exact integral_normSq_family_eq_diagonal_of_injective
    coefficient twoDistinctMonomials
    twoDistinctMonomials_signature_injective

/-- The same exact diagonal identity survives deterministic free harmonic
translation of the one phase coordinate. -/
theorem twoDistinctMonomials_freeHarmonic_diagonalSecondMoment_contract
    (coefficient : Fin 2 → Complex)
    (frequency : Fin 1 → Real) (time : Real) :
    (∫ phase : UnitAddTorus (Fin 1),
      Complex.normSq
        (finiteWeightedMonomialFamily coefficient twoDistinctMonomials
          (freeHarmonicPhaseEvolution frequency time phase))
      ∂finitePhaseHaarLaw (Fin 1)) =
      ∑ j, Complex.normSq (coefficient j) := by
  exact integral_normSq_family_freeHarmonic_eq_diagonal_of_injective
    coefficient twoDistinctMonomials frequency time
    twoDistinctMonomials_signature_injective

#print axioms twoDistinctMonomials_cross_eq_zero_contract
#print axioms twoDistinctMonomials_diagonalSecondMoment_contract
#print axioms twoDistinctMonomials_freeHarmonic_diagonalSecondMoment_contract
#print axioms integral_weightedMonomialCross_eq_zero_of_signature_ne
#print axioms integral_normSq_family_eq_diagonal_of_injective

end

end ArchonPhysicsConsumers.Thermalization.FinitePhaseMonomialHaarOrthogonality
