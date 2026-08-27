import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import ArchonPhysics.ActualTwoMassRegularSpectralPatch
import ArchonPhysics.ActualTwoMassCountableSpectralAtlas
import ArchonPhysics.MassWeightedCycleBridge
import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.PeriodicWeightedCycleBlockGluing
import ArchonPhysics.QuantitativeJacobianGoodBadPushforward
import ArchonPhysics.RandomMassOrderedProjectorBridge
import ArchonPhysics.TwoParameterSpectralPolynomialAvoidance

/-!
# An explicit actual-model two-mass spectral Jacobian polynomial

We specialize the genuine periodic random-mass harmonic matrix to three
sites, vary masses `0` and `1`, and freeze the third mass at one.  The two
children are the two positive decreasingly ordered modes `0` and `1`.

In inverse masses `x = m₀⁻¹`, `y = m₁⁻¹`, the characteristic
polynomial is

`E * (E² - 2 * (x + y + 1) * E + 3 * (x*y + x + y))`.

The Jacobian of the two elementary symmetric functions of the positive
eigenvalues has determinant `6 * (x - y)`.  The frequency square roots and
the raw-to-inverse-mass change of variables contribute only nonzero factors.
Thus actual spectral-Jacobian degeneracy is contained in the zero set of the
explicit nonzero polynomial `X 0 - X 1`, which the iid pair law avoids.
-/

open scoped Matrix

namespace ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial

open ArchonPhysics
open ArchonPhysics.ActualTwoMassCountableSpectralAtlas
open ArchonPhysics.ActualTwoMassRegularSpectralPatch
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.QuantitativeJacobianGoodBadPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.RandomMassSimpleSpectrum
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter Function MeasureTheory Set

noncomputable section

/-- The frozen three-site background; the actual chart replaces sites zero
and one and leaves the third mass equal to one. -/
def frozenUnitMassThree : Lattice.PositiveMassConfig 3 where
  mass _ := 1
  mass_pos _ := by norm_num

/-- Inverse masses for the two varied sites and the frozen unit-mass site. -/
def threeSiteInverseWeights (pair : Real × Real) : Fin 3 → Real :=
  ![pair.1⁻¹, pair.2⁻¹, 1]

/-- The explicit reindexed weighted three-cycle Laplacian. -/
def explicitThreeCycleLaplacian (pair : Real × Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  !![pair.1⁻¹ + pair.2⁻¹, -pair.2⁻¹, -pair.1⁻¹;
     -pair.2⁻¹, pair.2⁻¹ + 1, -1;
     -pair.1⁻¹, -1, pair.1⁻¹ + 1]

/-- Direct finite-matrix identification of the actual three-cycle
inverse-mass Laplacian. -/
theorem finWeightedCycleLaplacian_threeSiteInverseWeights
    (pair : Real × Real) :
    finWeightedCycleLaplacian (threeSiteInverseWeights pair) =
      explicitThreeCycleLaplacian pair := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_succ]
  <;> norm_num +decide [threeSiteInverseWeights, explicitThreeCycleLaplacian,
    finCycleEdgeVector, SingleMassRankOnePerturbation.cycleMassPerturbationVector,
    differenceMatrix, siteEquivFin]
  <;> simp

/-- Evaluation of the explicit three-cycle characteristic polynomial. -/
theorem explicitThreeCycleLaplacian_charpoly_eval
    (pair : Real × Real) (energy : Real) :
    (explicitThreeCycleLaplacian pair).charpoly.eval energy =
      energy * (energy ^ 2 -
        2 * (pair.1⁻¹ + pair.2⁻¹ + 1) * energy +
        3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹)) := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  simp [explicitThreeCycleLaplacian, Matrix.scalar_apply]
  ring


/-- The genuine three-site positive-mass family used below. -/
def actualThreeSiteMassConfig (pair : Real × Real) :
    Lattice.PositiveMassConfig 3 :=
  twoSiteMassConfig frozenUnitMassThree
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair

/-- Its genuine physical harmonic Hermitian matrix. -/
def actualThreeSiteHarmonic (pair : Real × Real) :
    HermitianMatrix (Lattice.Site 3) :=
  twoSiteHarmonicHermitian frozenUnitMassThree
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair

/-- The actual child chart consisting of the two decreasing positive modes. -/
def actualThreeSitePositiveChildChart (pair : Real × Real) : Real × Real :=
  actualTwoMassChildFrequencyChart frozenUnitMassThree
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair

theorem zero_ne_one_threeSite :
    (0 : Lattice.Site 3) ≠ 1 := by decide

/-- On the iid support, the inverse-mass coordinates of the genuine physical
configuration are exactly `(m₀⁻¹, m₁⁻¹, 1)`. -/
theorem inverseMassCoordinates_actualThreeSiteMassConfig
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport) :
    RandomMassResultantBridge.inverseMassCoordinates
        (actualThreeSiteMassConfig pair) =
      threeSiteInverseWeights pair := by
  funext k
  fin_cases k <;>
    simp [RandomMassResultantBridge.inverseMassCoordinates,
      actualThreeSiteMassConfig, threeSiteInverseWeights, siteEquivFin,
      twoSiteMassConfig, frozenUnitMassThree, clippedMass_eq_self,
      hpair.1, hpair.2]

/-- The characteristic equation of the genuine physical three-site matrix
has the displayed inverse-mass quadratic factor. -/
theorem actualThreeSiteHarmonic_charpoly_eval
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (energy : Real) :
    (Matrix.charpoly (Matrix.of (actualThreeSiteHarmonic pair).val)).eval energy =
      energy * (energy ^ 2 -
        2 * (pair.1⁻¹ + pair.2⁻¹ + 1) * energy +
        3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹)) := by
  let m := actualThreeSiteMassConfig pair
  have hchar :
      (massWeightedHarmonicMatrix m).charpoly =
        (finWeightedCycleLaplacian
          (RandomMassResultantBridge.inverseMassCoordinates m)).charpoly := by
    calc
      (massWeightedHarmonicMatrix m).charpoly =
          (massWeightedDifferenceMatrix m *
            Matrix.transpose (massWeightedDifferenceMatrix m)).charpoly :=
        Matrix.charpoly_mul_comm
          (Matrix.transpose (massWeightedDifferenceMatrix m))
          (massWeightedDifferenceMatrix m)
      _ = (weightedCycleLaplacian (fun i => (m.mass i)⁻¹)).charpoly := by
        rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
      _ = (weightedCycleLaplacian
          (weightsOfCoordinates
            (RandomMassResultantBridge.inverseMassCoordinates m))).charpoly := by
        rw [RandomMassResultantBridge.weightsOfCoordinates_inverseMassCoordinates]
      _ = (finWeightedCycleLaplacian
          (RandomMassResultantBridge.inverseMassCoordinates m)).charpoly := by
        symm
        exact Matrix.charpoly_reindex _ _
  change (massWeightedHarmonicMatrix m).charpoly.eval energy = _
  rw [hchar, inverseMassCoordinates_actualThreeSiteMassConfig hpair,
    finWeightedCycleLaplacian_threeSiteInverseWeights]
  exact explicitThreeCycleLaplacian_charpoly_eval pair energy


/-- The explicit characteristic polynomial over the energy variable. -/
def threeSiteCharacteristicPolynomial (pair : Real × Real) : Polynomial Real :=
  Polynomial.X *
    (Polynomial.X ^ 2 -
      Polynomial.C (2 * (pair.1⁻¹ + pair.2⁻¹ + 1)) * Polynomial.X +
      Polynomial.C
        (3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹)))

theorem actualThreeSiteHarmonic_charpoly
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport) :
    Matrix.charpoly (Matrix.of (actualThreeSiteHarmonic pair).val) =
      threeSiteCharacteristicPolynomial pair := by
  apply Polynomial.funext
  intro energy
  rw [actualThreeSiteHarmonic_charpoly_eval hpair]
  simp [threeSiteCharacteristicPolynomial]

/-- Two independent eigenvectors at a specified eigenvalue force that exact
value, rather than merely some value, to be a multiple characteristic root. -/
theorem rootMultiplicity_charpoly_gt_one_of_two_eigenvectors_at
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Real) {lambda : Real}
    (v : Fin 2 → (n → Real)) (hv : LinearIndependent Real v)
    (heigen : ∀ j, Matrix.mulVec A (v j) = lambda • (v j)) :
    1 < A.charpoly.rootMultiplicity lambda := by
  let T : Module.End Real (n → Real) := A.toLin'
  let u : Fin 2 → T.eigenspace lambda := fun j ↦
    ⟨v j, by
      rw [Module.End.mem_eigenspace_iff]
      simpa [T, Matrix.toLin'_apply'] using heigen j⟩
  have hu : LinearIndependent Real u := by
    apply LinearIndependent.of_comp (T.eigenspace lambda).subtype
    simpa [u, Function.comp_def] using hv
  have htwo : 2 ≤ Module.finrank Real (T.eigenspace lambda) := by
    simpa using hu.fintype_card_le_finrank
  have hle := LinearMap.finrank_eigenspace_le T lambda
  have hle' : Module.finrank Real (T.eigenspace lambda) ≤
      A.charpoly.rootMultiplicity lambda := by
    simpa [T, Matrix.charpoly_toLin'] using hle
  omega

/-- For the actual three-site periodic harmonic matrix, unequal varied
masses already force the full ordered spectrum to be simple.  Indeed a
positive double root of the explicit characteristic quadratic would force
all three inverse masses to coincide. -/
theorem actualThreeSiteHarmonic_simple_of_mass_ne
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hne : pair.1 ≠ pair.2) :
    SimpleOrderedSpectrum (actualThreeSiteHarmonic pair) := by
  apply simpleOrderedSpectrum_of_not_orderedPositiveDuplicate
    (actualThreeSiteMassConfig pair)
  intro hduplicate
  have hrepeated :=
    repeatedPositiveHarmonic_of_orderedPositiveDuplicate
      (actualThreeSiteMassConfig pair) hduplicate
  rcases hrepeated with ⟨lambda, hlambda, v, hv, heigen⟩
  let A := massWeightedHarmonicMatrix (actualThreeSiteMassConfig pair)
  have hmultiple : 1 < A.charpoly.rootMultiplicity lambda :=
    rootMultiplicity_charpoly_gt_one_of_two_eigenvectors_at A v hv heigen
  have hrootDerivative :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot
      (Matrix.charpoly_monic A).ne_zero).1 hmultiple
  have hcharSource := actualThreeSiteHarmonic_charpoly hpair
  have hmatrixOf :
      Matrix.of (actualThreeSiteHarmonic pair).val = A := by
    ext i j
    rfl
  rw [hmatrixOf] at hcharSource
  have hchar : A.charpoly = threeSiteCharacteristicPolynomial pair :=
    hcharSource
  have hrootThree :
      (threeSiteCharacteristicPolynomial pair).IsRoot lambda := by
    rw [← hchar]
    exact hrootDerivative.1
  have hroot :
      lambda = 0 ∨
        lambda ^ 2 - 2 * (pair.1⁻¹ + pair.2⁻¹ + 1) * lambda +
          3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹) = 0 := by
    simpa [Polynomial.IsRoot.def, threeSiteCharacteristicPolynomial] using
      hrootThree
  have hderivativeThree :
      (threeSiteCharacteristicPolynomial pair).derivative.eval lambda = 0 := by
    rw [← hchar]
    exact hrootDerivative.2
  have hderivative :
      3 * lambda ^ 2 -
        4 * (pair.1⁻¹ + pair.2⁻¹ + 1) * lambda +
        3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹) = 0 := by
    convert hderivativeThree using 1
    simp [threeSiteCharacteristicPolynomial]
    ring
  have hquadratic :
      lambda ^ 2 - 2 * (pair.1⁻¹ + pair.2⁻¹ + 1) * lambda +
        3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹) = 0 :=
    hroot.resolve_left hlambda.ne'
  have hlambdaSum : lambda = pair.1⁻¹ + pair.2⁻¹ + 1 := by
    nlinarith [hquadratic, hderivative]
  have hdiscriminant :
      (pair.1⁻¹ - pair.2⁻¹) ^ 2 +
        (pair.1⁻¹ - 1) ^ 2 + (pair.2⁻¹ - 1) ^ 2 = 0 := by
    nlinarith [hquadratic]
  have hinverseEq : pair.1⁻¹ = pair.2⁻¹ := by
    nlinarith [sq_nonneg (pair.1⁻¹ - pair.2⁻¹),
      sq_nonneg (pair.1⁻¹ - 1), sq_nonneg (pair.2⁻¹ - 1)]
  exact hne (inv_injective hinverseEq)

/-- The first two actual squared frequencies. -/
def actualThreeSiteFirstEnergy (pair : Real × Real) : Real :=
  orderedEigenvalue (actualThreeSiteHarmonic pair) 0

def actualThreeSiteSecondEnergy (pair : Real × Real) : Real :=
  orderedEigenvalue (actualThreeSiteHarmonic pair) 1

/-- Under simple spectrum, the first two three-site modes are exactly the
positive modes preceding the fixed last translation mode. -/
theorem actualThreeSite_first_second_energy_pos
    (pair : Real × Real)
    (hsimple : SimpleOrderedSpectrum (actualThreeSiteHarmonic pair)) :
    0 < actualThreeSiteFirstEnergy pair ∧
      0 < actualThreeSiteSecondEnergy pair := by
  have hfirstFrequency : 0 < orderedModeFrequency
      (actualThreeSiteHarmonic pair) 0 := by
    apply (orderedModeFrequency_pos_iff_ne_last
      (actualThreeSiteMassConfig pair) hsimple 0).2
    decide
  have hsecondFrequency : 0 < orderedModeFrequency
      (actualThreeSiteHarmonic pair) 1 := by
    apply (orderedModeFrequency_pos_iff_ne_last
      (actualThreeSiteMassConfig pair) hsimple 1).2
    decide
  exact ⟨by
    simpa [actualThreeSiteFirstEnergy, orderedModeFrequency] using hfirstFrequency,
    by
      simpa [actualThreeSiteSecondEnergy, orderedModeFrequency] using hsecondFrequency⟩

/-- The two positive actual eigenvalues have the explicit elementary
symmetric functions of the two inverse masses. -/
theorem actualThreeSite_positiveEnergy_symmetric
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum (actualThreeSiteHarmonic pair)) :
    actualThreeSiteFirstEnergy pair + actualThreeSiteSecondEnergy pair =
        2 * (pair.1⁻¹ + pair.2⁻¹ + 1) ∧
      actualThreeSiteFirstEnergy pair * actualThreeSiteSecondEnergy pair =
        3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹) := by
  let first := actualThreeSiteFirstEnergy pair
  let second := actualThreeSiteSecondEnergy pair
  let sumInv := pair.1⁻¹ + pair.2⁻¹ + 1
  let pairInv := pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹
  have hpositive := actualThreeSite_first_second_energy_pos pair hsimple
  have hrootFirst :
      first * (first ^ 2 - 2 * sumInv * first + 3 * pairInv) = 0 := by
    rw [← actualThreeSiteHarmonic_charpoly_eval hpair]
    exact charpoly_eval_orderedEigenvalue_eq_zero
      (actualThreeSiteHarmonic pair) 0
  have hrootSecond :
      second * (second ^ 2 - 2 * sumInv * second + 3 * pairInv) = 0 := by
    rw [← actualThreeSiteHarmonic_charpoly_eval hpair]
    exact charpoly_eval_orderedEigenvalue_eq_zero
      (actualThreeSiteHarmonic pair) 1
  have hquadraticFirst :
      first ^ 2 - 2 * sumInv * first + 3 * pairInv = 0 :=
    (mul_eq_zero.mp hrootFirst).resolve_left (ne_of_gt hpositive.1)
  have hquadraticSecond :
      second ^ 2 - 2 * sumInv * second + 3 * pairInv = 0 :=
    (mul_eq_zero.mp hrootSecond).resolve_left (ne_of_gt hpositive.2)
  have hne : first ≠ second := by
    exact hsimple.ne (by decide)
  have hfactor :
      (first - second) * (first + second - 2 * sumInv) = 0 := by
    nlinarith [hquadraticFirst, hquadraticSecond]
  have hsum : first + second = 2 * sumInv := by
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne))
  have hproduct : first * second = 3 * pairInv := by
    nlinarith [hquadraticFirst]
  exact ⟨hsum, hproduct⟩


/-- The explicit symmetric-energy map in the two raw masses. -/
def inverseMassEnergySymmetric (pair : Real × Real) : Real × Real :=
  (2 * (pair.1⁻¹ + pair.2⁻¹ + 1),
    3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹))

/-- Away from equal masses, the raw-mass derivative of the explicit
inverse-mass symmetric-energy map is injective.  This is the cleared
Jacobian numerator calculation: the elimination factor is `m₀⁻¹-m₁⁻¹`. -/
theorem exists_hasFDerivAt_inverseMassEnergySymmetric_injective
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hne : pair.1 ≠ pair.2) :
    ∃ derivative : (Real × Real) →L[Real] (Real × Real),
      HasFDerivAt inverseMassEnergySymmetric derivative pair ∧
        Function.Injective derivative := by
  have hfst : pair.1 ≠ 0 := ne_of_gt
    (massLower_pos.trans_le hpair.1.1)
  have hsnd : pair.2 ≠ 0 := ne_of_gt
    (massLower_pos.trans_le hpair.2.1)
  let dfst : (Real × Real) →L[Real] Real :=
    (ContinuousLinearMap.toSpanSingleton Real (-(pair.1 ^ 2)⁻¹)).comp
      (ContinuousLinearMap.fst Real Real Real)
  let dsnd : (Real × Real) →L[Real] Real :=
    (ContinuousLinearMap.toSpanSingleton Real (-(pair.2 ^ 2)⁻¹)).comp
      (ContinuousLinearMap.snd Real Real Real)
  have hdfst : HasFDerivAt (fun nearby : Real × Real => nearby.1⁻¹)
      dfst pair := by
    simpa [dfst, Function.comp_def] using
      (hasFDerivAt_inv hfst).comp pair hasFDerivAt_fst
  have hdsnd : HasFDerivAt (fun nearby : Real × Real => nearby.2⁻¹)
      dsnd pair := by
    simpa [dsnd, Function.comp_def] using
      (hasFDerivAt_inv hsnd).comp pair hasFDerivAt_snd
  let firstDerivative : (Real × Real) →L[Real] Real :=
    (2 : Real) • (dfst + dsnd)
  let secondDerivative : (Real × Real) →L[Real] Real :=
    (3 : Real) • (pair.1⁻¹ • dsnd + pair.2⁻¹ • dfst + dfst + dsnd)
  let derivative : (Real × Real) →L[Real] (Real × Real) :=
    firstDerivative.prod secondDerivative
  have hfirst : HasFDerivAt
      (fun nearby : Real × Real =>
        2 * (nearby.1⁻¹ + nearby.2⁻¹ + 1))
      firstDerivative pair := by
    simpa [firstDerivative, add_assoc] using
      ((hdfst.add hdsnd).add_const 1).const_mul 2
  have hsecond : HasFDerivAt
      (fun nearby : Real × Real =>
        3 * (nearby.1⁻¹ * nearby.2⁻¹ + nearby.1⁻¹ + nearby.2⁻¹))
      secondDerivative pair := by
    simpa [secondDerivative, add_assoc] using
      (((hdfst.mul hdsnd).add hdfst).add hdsnd).const_mul 3
  refine ⟨derivative, ?_, ?_⟩
  · convert hfirst.prodMk hsecond using 1 <;> rfl
  · intro u v huv
    have hz : derivative (u - v) = 0 := by
      calc
        derivative (u - v) = derivative u - derivative v :=
          map_sub derivative u v
        _ = 0 := sub_eq_zero.mpr huv
    have hzeroFirstFormula :
        -(2 * ((u.1 - v.1) * (pair.1 ^ 2)⁻¹)) +
          -(2 * ((u.2 - v.2) * (pair.2 ^ 2)⁻¹)) = 0 := by
      simpa [derivative, firstDerivative, secondDerivative, dfst, dsnd,
        ContinuousLinearMap.comp_apply] using congrArg Prod.fst hz
    have hzeroSecondFormula :
        -(3 * (pair.1⁻¹ * ((u.2 - v.2) * (pair.2 ^ 2)⁻¹))) +
          -(3 * (pair.2⁻¹ * ((u.1 - v.1) * (pair.1 ^ 2)⁻¹))) +
          -(3 * ((u.1 - v.1) * (pair.1 ^ 2)⁻¹)) +
          -(3 * ((u.2 - v.2) * (pair.2 ^ 2)⁻¹)) = 0 := by
      simpa [derivative, firstDerivative, secondDerivative, dfst, dsnd,
        ContinuousLinearMap.comp_apply] using congrArg Prod.snd hz
    have hinvNe : pair.1⁻¹ ≠ pair.2⁻¹ := inv_injective.ne hne
    have hsumScaled :
        (u.1 - v.1) * (pair.1 ^ 2)⁻¹ +
          (u.2 - v.2) * (pair.2 ^ 2)⁻¹ = 0 := by
      linarith [hzeroFirstFormula]
    have hsumScaledByFirst :
        pair.1⁻¹ * ((u.1 - v.1) * (pair.1 ^ 2)⁻¹) +
          pair.1⁻¹ * ((u.2 - v.2) * (pair.2 ^ 2)⁻¹) = 0 := by
      calc
        _ = pair.1⁻¹ *
            ((u.1 - v.1) * (pair.1 ^ 2)⁻¹ +
              (u.2 - v.2) * (pair.2 ^ 2)⁻¹) := by ring
        _ = 0 := by rw [hsumScaled, mul_zero]
    have hfactorExpanded :
        pair.2⁻¹ * ((u.1 - v.1) * (pair.1 ^ 2)⁻¹) -
          pair.1⁻¹ * ((u.1 - v.1) * (pair.1 ^ 2)⁻¹) = 0 := by
      linarith [hzeroSecondFormula, hsumScaled, hsumScaledByFirst]
    have hfactor :
        (pair.2⁻¹ - pair.1⁻¹) *
          ((u.1 - v.1) * (pair.1 ^ 2)⁻¹) = 0 := by
      calc
        _ = pair.2⁻¹ * ((u.1 - v.1) * (pair.1 ^ 2)⁻¹) -
            pair.1⁻¹ * ((u.1 - v.1) * (pair.1 ^ 2)⁻¹) := by ring
        _ = 0 := hfactorExpanded
    have hscaledFirst :
        (u.1 - v.1) * (pair.1 ^ 2)⁻¹ = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left
        (sub_ne_zero.mpr hinvNe.symm)
    have hfstZero : (u - v).1 = 0 := by
      change u.1 - v.1 = 0
      exact (mul_eq_zero.mp hscaledFirst).resolve_right
        (inv_ne_zero (pow_ne_zero 2 hfst))
    have hscaledSecond :
        (u.2 - v.2) * (pair.2 ^ 2)⁻¹ = 0 := by
      nlinarith [hzeroFirstFormula, hscaledFirst]
    have hsndZero : (u - v).2 = 0 := by
      change u.2 - v.2 = 0
      exact (mul_eq_zero.mp hscaledSecond).resolve_right
        (inv_ne_zero (pow_ne_zero 2 hsnd))
    exact sub_eq_zero.mp (Prod.ext hfstZero hsndZero)


/-- Squaring two frequencies and taking their elementary symmetric pair. -/
def frequencyEnergySymmetric (frequency : Real × Real) : Real × Real :=
  (frequency.1 ^ 2 + frequency.2 ^ 2,
    frequency.1 ^ 2 * frequency.2 ^ 2)

/-- Along the actual simple three-site branch, the squared-frequency
symmetric pair is the explicit inverse-mass polynomial map. -/
theorem frequencyEnergySymmetric_actualThreeSitePositiveChildChart
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum (actualThreeSiteHarmonic pair)) :
    frequencyEnergySymmetric (actualThreeSitePositiveChildChart pair) =
      inverseMassEnergySymmetric pair := by
  have hpositive := actualThreeSite_first_second_energy_pos pair hsimple
  have hsymmetric := actualThreeSite_positiveEnergy_symmetric hpair hsimple
  apply Prod.ext
  · change
      (Real.sqrt (actualThreeSiteFirstEnergy pair)) ^ 2 +
          (Real.sqrt (actualThreeSiteSecondEnergy pair)) ^ 2 =
        2 * (pair.1⁻¹ + pair.2⁻¹ + 1)
    rw [Real.sq_sqrt hpositive.1.le, Real.sq_sqrt hpositive.2.le,
      hsymmetric.1]
  · change
      (Real.sqrt (actualThreeSiteFirstEnergy pair)) ^ 2 *
          (Real.sqrt (actualThreeSiteSecondEnergy pair)) ^ 2 =
        3 * (pair.1⁻¹ * pair.2⁻¹ + pair.1⁻¹ + pair.2⁻¹)
    rw [Real.sq_sqrt hpositive.1.le, Real.sq_sqrt hpositive.2.le,
      hsymmetric.2]

/-- The actual two-positive-mode frequency Jacobian is nondegenerate at
every interior simple-spectrum pair with unequal varied masses.  No chart
regularity or Jacobian hypothesis is assumed. -/
theorem actualThreeSitePositiveChildJacobian_det_ne_zero_of_simple_of_mass_ne
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum (actualThreeSiteHarmonic pair))
    (hne : pair.1 ≠ pair.2) :
    (actualTwoMassChildFrequencyJacobian frozenUnitMassThree
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det ≠ 0 := by
  have hsupport : pair ∈ iidMassPairSupport := interior_subset hpair
  have hpositive := actualThreeSite_first_second_energy_pos pair hsimple
  obtain ⟨chartDerivative, hchartDerivative⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassChildFrequencyChart
      frozenUnitMassThree zero_ne_one_threeSite hpair hsimple 0 1
        hpositive.1 hpositive.2
  let J := actualTwoMassChildFrequencyJacobian frozenUnitMassThree
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair
  have hJ : J = chartDerivative := by
    simpa [J, actualTwoMassChildFrequencyJacobian] using
      hchartDerivative.hasFDerivAt.fderiv
  have hchartJ : HasFDerivAt actualThreeSitePositiveChildChart J pair := by
    rw [hJ]
    exact hchartDerivative.hasFDerivAt
  have houter : DifferentiableAt Real frequencyEnergySymmetric
      (actualThreeSitePositiveChildChart pair) := by
    unfold frequencyEnergySymmetric
    fun_prop
  have hcomposition : HasFDerivAt
      (fun nearby =>
        frequencyEnergySymmetric (actualThreeSitePositiveChildChart nearby))
      (fderiv Real frequencyEnergySymmetric
          (actualThreeSitePositiveChildChart pair) ∘L J) pair := by
    simpa [Function.comp_def] using
      houter.hasFDerivAt.comp pair hchartJ
  have heventuallyIdentity :
      (fun nearby =>
        frequencyEnergySymmetric (actualThreeSitePositiveChildChart nearby)) =ᶠ[nhds pair]
        inverseMassEnergySymmetric := by
    filter_upwards [isOpen_interior.mem_nhds hpair,
      eventually_simple_twoSiteHarmonicHermitian frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair hsimple] with
        nearby hnearby hsimpleNearby
    exact frequencyEnergySymmetric_actualThreeSitePositiveChildChart
      (interior_subset hnearby) hsimpleNearby
  have hinverseByComposition : HasFDerivAt inverseMassEnergySymmetric
      (fderiv Real frequencyEnergySymmetric
          (actualThreeSitePositiveChildChart pair) ∘L J) pair :=
    hcomposition.congr_of_eventuallyEq heventuallyIdentity.symm
  obtain ⟨explicitDerivative, hexplicitDerivative, hexplicitInjective⟩ :=
    exists_hasFDerivAt_inverseMassEnergySymmetric_injective hsupport hne
  have hderivativeEquality :
      explicitDerivative =
        fderiv Real frequencyEnergySymmetric
          (actualThreeSitePositiveChildChart pair) ∘L J :=
    hexplicitDerivative.unique hinverseByComposition
  have hJInjective : Function.Injective J := by
    intro u v huv
    apply hexplicitInjective
    rw [hderivativeEquality]
    exact congrArg
      (fderiv Real frequencyEnergySymmetric
        (actualThreeSitePositiveChildChart pair)) huv
  have hker : J.ker = ⊥ := LinearMap.ker_eq_bot.mpr hJInjective
  have hdetLinear : LinearMap.det J.toLinearMap ≠ 0 := by
    intro hzero
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) hker
  simpa [J, ContinuousLinearMap.det] using hdetLinear


/-- The cleared numerator of the actual three-site child-frequency
Jacobian, expressed in the two inverse-mass coordinates. -/
def threeSiteJacobianPolynomial : MvPolynomial (Fin 2) Real :=
  MvPolynomial.X 0 - MvPolynomial.X 1

@[simp] theorem threeSiteJacobianPolynomial_eval_inverseMassPair
    (pair : Real × Real) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
        threeSiteJacobianPolynomial = pair.1⁻¹ - pair.2⁻¹ := by
  simp [threeSiteJacobianPolynomial]

theorem threeSiteJacobianPolynomial_ne_zero :
    threeSiteJacobianPolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (![1, 0] : Fin 2 → Real)) hzero
  norm_num [threeSiteJacobianPolynomial] at heval

/-- The determinant hypothesis is completely eliminated for the explicit
three-site branch: interior unequal raw masses suffice. -/
theorem actualThreeSitePositiveChildJacobian_det_ne_zero_of_mass_ne
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hne : pair.1 ≠ pair.2) :
    (actualTwoMassChildFrequencyJacobian frozenUnitMassThree
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det ≠ 0 := by
  exact
    actualThreeSitePositiveChildJacobian_det_ne_zero_of_simple_of_mass_ne
      hpair
      (actualThreeSiteHarmonic_simple_of_mass_ne (interior_subset hpair) hne)
      hne

/-- The genuine Jacobian-degeneracy locus in the interior is contained in
the zero set of the explicit nonzero inverse-mass polynomial. -/
theorem iidMassPairLaw_actualThreeSitePositiveChildJacobian_degenerate_interior_eq_zero :
    iidMassPairLaw
      {pair |
        pair ∈ interior iidMassPairSupport ∧
        (actualTwoMassChildFrequencyJacobian frozenUnitMassThree
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det = 0} = 0 := by
  apply measure_mono_null (t :=
    {pair |
      MvPolynomial.eval (iidInverseMassPairCoordinates pair)
        threeSiteJacobianPolynomial = 0})
  · intro pair hbad
    simp only [Set.mem_ofPred_eq,
      threeSiteJacobianPolynomial_eval_inverseMassPair]
    by_contra hinverse
    have hne : pair.1 ≠ pair.2 := by
      intro heq
      apply hinverse
      simp [heq]
    exact
      (actualThreeSitePositiveChildJacobian_det_ne_zero_of_mass_ne
        hbad.1 hne) hbad.2
  · exact iidMassPairLaw_zeroSet_eval_inverseCoordinates
      threeSiteJacobianPolynomial threeSiteJacobianPolynomial_ne_zero

/-- One raw-coordinate polynomial removes both the boundary of the support
square and the diagonal. -/
def threeSiteRegularityPolynomial : MvPolynomial (Fin 2) Real :=
  (MvPolynomial.X 0 - MvPolynomial.C massLower) *
    (MvPolynomial.X 0 - MvPolynomial.C massUpper) *
    (MvPolynomial.X 1 - MvPolynomial.C massLower) *
    (MvPolynomial.X 1 - MvPolynomial.C massUpper) *
    (MvPolynomial.X 0 - MvPolynomial.X 1)

@[simp] theorem threeSiteRegularityPolynomial_eval_massPair
    (pair : Real × Real) :
    MvPolynomial.eval (iidMassPairCoordinates pair)
        threeSiteRegularityPolynomial =
      (pair.1 - massLower) * (pair.1 - massUpper) *
        (pair.2 - massLower) * (pair.2 - massUpper) *
        (pair.1 - pair.2) := by
  simp [threeSiteRegularityPolynomial]

theorem threeSiteRegularityPolynomial_ne_zero :
    threeSiteRegularityPolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (![1, (11 / 10 : Real)] : Fin 2 → Real)) hzero
  norm_num [threeSiteRegularityPolynomial, massLower, massUpper] at heval

/-- The iid pair lies in the genuine three-site regular source almost
everywhere.  Thus this one actual chart has IFT patches at almost every mass
pair; no simplicity, positivity, or Jacobian assumption remains. -/
theorem actualThreeSiteRegularSource_ae :
    ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ actualTwoMassRegularSource frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 := by
  have hsupport : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ iidMassPairSupport := by
    rw [iidMassPairLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
    · filter_upwards [massCoordinate_mem_support_ae] with first hfirst
      filter_upwards [massCoordinate_mem_support_ae] with second hsecond
      exact ⟨hfirst, hsecond⟩
    · exact (measurableSet_Icc.prod measurableSet_Icc)
  have hpolynomial : ∀ᵐ pair ∂iidMassPairLaw,
      MvPolynomial.eval (iidMassPairCoordinates pair)
        threeSiteRegularityPolynomial ≠ 0 := by
    exact measure_eq_zero_iff_ae_notMem.mp
      (iidMassPairLaw_zeroSet_mvPolynomial_eval
        threeSiteRegularityPolynomial threeSiteRegularityPolynomial_ne_zero)
  filter_upwards [hsupport, hpolynomial] with pair hpair hpoly
  have heval :
      (pair.1 - massLower) * (pair.1 - massUpper) *
        (pair.2 - massLower) * (pair.2 - massUpper) *
        (pair.1 - pair.2) ≠ 0 := by
    simpa only [threeSiteRegularityPolynomial_eval_massPair] using hpoly
  rcases mul_ne_zero_iff.mp heval with ⟨h0123, hneFactor⟩
  rcases mul_ne_zero_iff.mp h0123 with ⟨h012, hsecondUpper⟩
  rcases mul_ne_zero_iff.mp h012 with ⟨h01, hsecondLower⟩
  rcases mul_ne_zero_iff.mp h01 with ⟨hfirstLower, hfirstUpper⟩
  have hne : pair.1 ≠ pair.2 := sub_ne_zero.mp hneFactor
  have hinterior : pair ∈ interior iidMassPairSupport := by
    rw [iidMassPairSupport, interior_prod_eq, massSupport,
      interior_Icc]
    exact ⟨
      ⟨lt_of_le_of_ne hpair.1.1 (sub_ne_zero.mp hfirstLower).symm,
        lt_of_le_of_ne hpair.1.2 (sub_ne_zero.mp hfirstUpper)⟩,
      ⟨lt_of_le_of_ne hpair.2.1 (sub_ne_zero.mp hsecondLower).symm,
        lt_of_le_of_ne hpair.2.2 (sub_ne_zero.mp hsecondUpper)⟩⟩
  have hsimple := actualThreeSiteHarmonic_simple_of_mass_ne hpair hne
  have hpositive := actualThreeSite_first_second_energy_pos pair hsimple
  have hdet :=
    actualThreeSitePositiveChildJacobian_det_ne_zero_of_mass_ne hinterior hne
  exact ⟨hinterior, hsimple, hpositive.1, hpositive.2, hdet⟩


/-- Reciprocal-natural determinant level inside the actual regular source. -/
def actualThreeSiteGoodDetLevel (n : Nat) : Set (Real × Real) :=
  {pair |
    pair ∈ actualTwoMassRegularSource frozenUnitMassThree
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 ∧
    1 / ((n : Real) + 1) ≤
      |(actualTwoMassChildFrequencyJacobian frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det|}

theorem actualThreeSiteGoodDetLevel_det_lower
    {n : Nat} {pair : Real × Real}
    (hpair : pair ∈ actualThreeSiteGoodDetLevel n) :
    1 / ((n : Real) + 1) ≤
      |(actualTwoMassChildFrequencyJacobian frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det| :=
  hpair.2

theorem actualThreeSiteRegularSource_subset_iUnion_goodDetLevel :
    actualTwoMassRegularSource frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 ⊆
      ⋃ n, actualThreeSiteGoodDetLevel n := by
  intro pair hregular
  have hdet :
      (actualTwoMassChildFrequencyJacobian frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det ≠ 0 :=
    hregular.2.2.2.2
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hdet)
  exact mem_iUnion.mpr ⟨n, hregular, hn.le⟩

theorem actualThreeSiteGoodDetLevels_ae :
    ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ ⋃ n, actualThreeSiteGoodDetLevel n := by
  filter_upwards [actualThreeSiteRegularSource_ae] with pair hpair
  exact actualThreeSiteRegularSource_subset_iUnion_goodDetLevel hpair


theorem measurable_actualThreeSitePositiveChildJacobian_det :
    Measurable fun pair : Real × Real =>
      (actualTwoMassChildFrequencyJacobian frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det := by
  change Measurable fun pair : Real × Real =>
    (fderiv Real actualThreeSitePositiveChildChart pair).det
  exact ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_fderiv Real actualThreeSitePositiveChildChart)

theorem measurableSet_actualThreeSiteRegularSource :
    MeasurableSet
      (actualTwoMassRegularSource frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1) := by
  have hsimpleOpen : IsOpen
      {pair : Real × Real |
        SimpleOrderedSpectrum
          (twoSiteHarmonicHermitian frozenUnitMassThree
            (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair)} := by
    rw [isOpen_iff_mem_nhds]
    intro pair hsimple
    exact eventually_simple_twoSiteHarmonicHermitian frozenUnitMassThree
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair hsimple
  have hfirstContinuous : Continuous fun pair : Real × Real =>
      orderedEigenvalue
        (twoSiteHarmonicHermitian frozenUnitMassThree
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair) 0 :=
    (continuous_orderedEigenvalue 0).comp
      (continuous_twoSiteHarmonicHermitian frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3))
  have hsecondContinuous : Continuous fun pair : Real × Real =>
      orderedEigenvalue
        (twoSiteHarmonicHermitian frozenUnitMassThree
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair) 1 :=
    (continuous_orderedEigenvalue 1).comp
      (continuous_twoSiteHarmonicHermitian frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3))
  have hfirstOpen : IsOpen
      {pair : Real × Real |
        0 < orderedEigenvalue
          (twoSiteHarmonicHermitian frozenUnitMassThree
            (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair) 0} :=
    hfirstContinuous.isOpen_preimage _ isOpen_Ioi
  have hsecondOpen : IsOpen
      {pair : Real × Real |
        0 < orderedEigenvalue
          (twoSiteHarmonicHermitian frozenUnitMassThree
            (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair) 1} :=
    hsecondContinuous.isOpen_preimage _ isOpen_Ioi
  have hdetMeasurable : MeasurableSet
      {pair : Real × Real |
        (actualTwoMassChildFrequencyJacobian frozenUnitMassThree
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det ≠ 0} := by
    exact (measurableSet_singleton 0).compl.preimage
      measurable_actualThreeSitePositiveChildJacobian_det
  exact isOpen_interior.measurableSet.inter
    (hsimpleOpen.measurableSet.inter
      (hfirstOpen.measurableSet.inter
        (hsecondOpen.measurableSet.inter hdetMeasurable)))

theorem measurableSet_actualThreeSiteGoodDetLevel (n : Nat) :
    MeasurableSet (actualThreeSiteGoodDetLevel n) := by
  have habsMeasurable : Measurable fun pair : Real × Real =>
      |(actualTwoMassChildFrequencyJacobian frozenUnitMassThree
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) 0 1 pair).det| :=
    measurable_actualThreeSitePositiveChildJacobian_det.abs
  exact measurableSet_actualThreeSiteRegularSource.inter
    (measurableSet_Ici.preimage habsMeasurable)

theorem monotone_actualThreeSiteGoodDetLevel :
    Monotone actualThreeSiteGoodDetLevel := by
  intro n m hnm pair hpair
  refine ⟨hpair.1, ?_⟩
  exact (one_div_le_one_div_of_le (by positivity) (by
    exact_mod_cast Nat.add_le_add_right hnm 1)).trans hpair.2

theorem tendsto_iidMassPairLaw_compl_actualThreeSiteGoodDetLevel_zero :
    Tendsto
      (fun n => iidMassPairLaw (actualThreeSiteGoodDetLevel n)ᶜ)
      atTop (nhds 0) := by
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  exact
    tendsto_measure_compl_good_zero_of_monotone_of_ae_iUnion
        iidMassPairLaw actualThreeSiteGoodDetLevel
          measurableSet_actualThreeSiteGoodDetLevel
          monotone_actualThreeSiteGoodDetLevel
          actualThreeSiteGoodDetLevels_ae

end

end ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial
