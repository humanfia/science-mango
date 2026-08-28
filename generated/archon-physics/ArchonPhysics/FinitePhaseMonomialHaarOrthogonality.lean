import ArchonPhysics.FiniteDuhamelPhaseAverage
import ArchonPhysics.FiniteHarmonicHaarPhasePropagation

/-!
# Exact finite Haar orthogonality for signed phase monomials

A finite signed phase monomial is a character of the finite product phase
torus.  Its integer exponent signature is therefore its complete label for
Haar orthogonality.  This module records that statement directly in the
signed-monomial language used by the FPUT Duhamel expansions:

* two weighted monomials with different signatures have zero cross moment;
* a diagonal cross moment is exactly the coefficient norm square;
* an arbitrary finite family retains precisely the equal-signature pairs;
* if the family has pairwise distinct signatures, its expected squared norm
  is the sum of the diagonal coefficient norm squares.

The same identities hold after deterministic free harmonic phase evolution,
because that evolution is a Haar-preserving translation.

These are exact finite-dimensional initial/free-phase statements.  They do
not assert nonlinear propagation of RPA, nor do they claim that a concrete
family of effective four-wave diagrams has distinct signatures.
-/

namespace ArchonPhysics.FinitePhaseMonomialHaarOrthogonality

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.RandomPhaseMoments

noncomputable section

variable {d J : Type*} [Fintype d] [DecidableEq d]

/-- The complete integer/exponent signature of a signed phase monomial. -/
def phaseSignature (factors : List (SignedMode d)) : d → Int :=
  monomialCharge factors

/-- Cross integrand of two deterministically weighted signed monomials. -/
def weightedMonomialCross
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d))
    (phase : UnitAddTorus d) : Complex :=
  weightedSignedMonomial leftCoefficient leftFactors phase *
    starRingEnd Complex
      (weightedSignedMonomial rightCoefficient rightFactors phase)

/-- The cross integrand is the coefficient cross product times the character
whose signature is the difference of the two monomial signatures. -/
theorem weightedMonomialCross_eq_differenceCharacter
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d))
    (phase : UnitAddTorus d) :
    weightedMonomialCross leftCoefficient rightCoefficient
        leftFactors rightFactors phase =
      (leftCoefficient * starRingEnd Complex rightCoefficient) *
        mFourier
          (phaseSignature leftFactors - phaseSignature rightFactors) phase := by
  unfold weightedMonomialCross weightedSignedMonomial phaseSignature
  rw [unitSignedMonomial_eq_mFourier,
    unitSignedMonomial_eq_mFourier, map_mul]
  calc
    leftCoefficient * (mFourier (monomialCharge leftFactors)) phase *
        (starRingEnd Complex rightCoefficient *
          starRingEnd Complex
            ((mFourier (monomialCharge rightFactors)) phase)) =
      (leftCoefficient * starRingEnd Complex rightCoefficient) *
        ((mFourier (monomialCharge leftFactors)) phase *
          starRingEnd Complex
            ((mFourier (monomialCharge rightFactors)) phase)) := by ring
    _ = (leftCoefficient * starRingEnd Complex rightCoefficient) *
        (mFourier
          (monomialCharge leftFactors - monomialCharge rightFactors)) phase := by
      rw [mFourier_mul_star_mFourier]

/-- Exact Haar cross moment: equal signatures retain the deterministic
coefficient cross product, while different signatures are orthogonal. -/
theorem integral_weightedMonomialCross_eq_ite
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      weightedMonomialCross leftCoefficient rightCoefficient
        leftFactors rightFactors phase
      ∂finitePhaseHaarLaw d) =
      if phaseSignature leftFactors = phaseSignature rightFactors then
        leftCoefficient * starRingEnd Complex rightCoefficient
      else 0 := by
  simp_rw [weightedMonomialCross_eq_differenceCharacter]
  rw [integral_const_mul, integral_mFourier_eq_ite]
  simp only [sub_eq_zero]
  split_ifs <;> simp

/-- Different integer/exponent signatures give an exactly vanishing Haar
cross term. -/
theorem integral_weightedMonomialCross_eq_zero_of_signature_ne
    (leftCoefficient rightCoefficient : Complex)
    (leftFactors rightFactors : List (SignedMode d))
    (hsignature : phaseSignature leftFactors ≠
      phaseSignature rightFactors) :
    (∫ phase : UnitAddTorus d,
      weightedMonomialCross leftCoefficient rightCoefficient
        leftFactors rightFactors phase
      ∂finitePhaseHaarLaw d) = 0 := by
  rw [integral_weightedMonomialCross_eq_ite]
  exact if_neg hsignature

omit [DecidableEq d] in
/-- A diagonal monomial has constant unit phase modulus, so its Haar second
moment is exactly the norm square of its deterministic coefficient. -/
theorem integral_normSq_weightedSignedMonomial
    (coefficient : Complex) (factors : List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      Complex.normSq (weightedSignedMonomial coefficient factors phase)
      ∂finitePhaseHaarLaw d) =
      Complex.normSq coefficient := by
  classical
  have hcomplex :
      (∫ phase : UnitAddTorus d,
        (Complex.normSq
          (weightedSignedMonomial coefficient factors phase) : Complex)
        ∂finitePhaseHaarLaw d) =
        (Complex.normSq coefficient : Complex) := by
    simpa only [weightedMonomialCross, Complex.mul_conj, if_true] using
      (integral_weightedMonomialCross_eq_ite
        (d := d) coefficient coefficient factors factors)
  norm_cast at hcomplex

/-- A finite deterministic linear combination of signed phase monomials. -/
def finiteWeightedMonomialFamily
    [Fintype J]
    (coefficient : J → Complex)
    (factors : J → List (SignedMode d))
    (phase : UnitAddTorus d) : Complex :=
  ∑ j, weightedSignedMonomial (coefficient j) (factors j) phase

/-- The signed-monomial family is literally the corresponding finite
character correction indexed by its exponent signatures. -/
theorem finiteWeightedMonomialFamily_eq_finitePhaseCorrection
    [Fintype J]
    (coefficient : J → Complex)
    (factors : J → List (SignedMode d))
    (phase : UnitAddTorus d) :
    finiteWeightedMonomialFamily coefficient factors phase =
      finitePhaseCorrection coefficient
        (fun j ↦ phaseSignature (factors j)) phase := by
  simp only [finiteWeightedMonomialFamily, finitePhaseCorrection,
    weightedSignedMonomial, unitSignedMonomial_eq_mFourier, phaseSignature]

/-- Exact finite-family cross-moment decomposition.  Signature collisions
are kept as coherent ordered-pair terms rather than silently discarded. -/
theorem integral_family_mul_star_eq_equalSignaturePairSum
    [Fintype J]
    (coefficient : J → Complex)
    (factors : J → List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      finiteWeightedMonomialFamily coefficient factors phase *
        starRingEnd Complex
          (finiteWeightedMonomialFamily coefficient factors phase)
      ∂finitePhaseHaarLaw d) =
      ∑ j, ∑ k,
        if phaseSignature (factors j) = phaseSignature (factors k) then
          coefficient j * starRingEnd Complex (coefficient k)
        else 0 := by
  simpa only [finiteWeightedMonomialFamily_eq_finitePhaseCorrection] using
    (integral_finitePhaseCorrection_mul_star_eq_equalChargePairSum
      coefficient (fun j ↦ phaseSignature (factors j)))

/-- Real-valued form of the exact finite-family equivalence-class
decomposition. -/
theorem integral_normSq_family_eq_equalSignaturePairSum
    [Fintype J]
    (coefficient : J → Complex)
    (factors : J → List (SignedMode d)) :
    (∫ phase : UnitAddTorus d,
      (Complex.normSq
        (finiteWeightedMonomialFamily coefficient factors phase) : Complex)
      ∂finitePhaseHaarLaw d) =
      ∑ j, ∑ k,
        if phaseSignature (factors j) = phaseSignature (factors k) then
          coefficient j * starRingEnd Complex (coefficient k)
        else 0 := by
  simpa only [Complex.mul_conj] using
    (integral_family_mul_star_eq_equalSignaturePairSum
      (d := d) coefficient factors)

/-- Under pairwise distinct signatures, the equal-signature ordered-pair sum
collapses exactly to its diagonal. -/
theorem equalSignaturePairSum_eq_diagonal_of_injective
    [Fintype J]
    (coefficient : J → Complex)
    (factors : J → List (SignedMode d))
    (hinjective : Function.Injective
      (fun j ↦ phaseSignature (factors j))) :
    (∑ j, ∑ k,
      if phaseSignature (factors j) = phaseSignature (factors k) then
        coefficient j * starRingEnd Complex (coefficient k)
      else 0) =
      ∑ j, (Complex.normSq (coefficient j) : Complex) := by
  classical
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.sum_eq_single j]
  · simp [Complex.mul_conj]
  · intro k _hk hkj
    rw [if_neg]
    intro hsignature
    exact hkj (hinjective hsignature).symm
  · simp

/-- Finite exact RPA/Haar isometry: if the exponent signatures are pairwise
distinct, the expected squared norm is the diagonal coefficient square
mass. -/
theorem integral_normSq_family_eq_diagonal_of_injective
    [Fintype J]
    (coefficient : J → Complex)
    (factors : J → List (SignedMode d))
    (hinjective : Function.Injective
      (fun j ↦ phaseSignature (factors j))) :
    (∫ phase : UnitAddTorus d,
      Complex.normSq
        (finiteWeightedMonomialFamily coefficient factors phase)
      ∂finitePhaseHaarLaw d) =
      ∑ j, Complex.normSq (coefficient j) := by
  have hcomplex :=
    integral_normSq_family_eq_equalSignaturePairSum
      (d := d) coefficient factors
  rw [equalSignaturePairSum_eq_diagonal_of_injective
    coefficient factors hinjective] at hcomplex
  norm_cast at hcomplex

omit [DecidableEq d] in
/-- Deterministic free harmonic evolution leaves the finite-family Haar
second moment unchanged.  This is a free-flow statement only. -/
theorem integral_normSq_family_freeHarmonicEvolution
    [Fintype J]
    (coefficient : J → Complex)
    (factors : J → List (SignedMode d))
    (frequency : d → Real) (time : Real) :
    (∫ phase : UnitAddTorus d,
      Complex.normSq
        (finiteWeightedMonomialFamily coefficient factors
          (freeHarmonicPhaseEvolution frequency time phase))
      ∂finitePhaseHaarLaw d) =
    ∫ phase : UnitAddTorus d,
      Complex.normSq
        (finiteWeightedMonomialFamily coefficient factors phase)
      ∂finitePhaseHaarLaw d := by
  have hpreserve :=
    measurePreserving_freeHarmonicPhaseEvolution frequency time
  have hembed : MeasurableEmbedding
      (freeHarmonicPhaseEvolution frequency time) := by
    unfold freeHarmonicPhaseEvolution
    exact measurableEmbedding_addLeft _
  exact hpreserve.integral_comp hembed
    (fun phase : UnitAddTorus d ↦
      Complex.normSq
        (finiteWeightedMonomialFamily coefficient factors phase))

/-- Pairwise-distinct exact RPA/Haar isometry after deterministic free
harmonic propagation. -/
theorem integral_normSq_family_freeHarmonic_eq_diagonal_of_injective
    [Fintype J]
    (coefficient : J → Complex)
    (factors : J → List (SignedMode d))
    (frequency : d → Real) (time : Real)
    (hinjective : Function.Injective
      (fun j ↦ phaseSignature (factors j))) :
    (∫ phase : UnitAddTorus d,
      Complex.normSq
        (finiteWeightedMonomialFamily coefficient factors
          (freeHarmonicPhaseEvolution frequency time phase))
      ∂finitePhaseHaarLaw d) =
      ∑ j, Complex.normSq (coefficient j) := by
  rw [integral_normSq_family_freeHarmonicEvolution]
  exact integral_normSq_family_eq_diagonal_of_injective
    coefficient factors hinjective

end

end ArchonPhysics.FinitePhaseMonomialHaarOrthogonality
