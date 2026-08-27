import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import ArchonPhysics.ActualTwoMassSpectralChart
import ArchonPhysics.FixedEnergySpectrumAvoidance

/-!
# Differentiability of actual two-mass simple spectral branches

For the genuine periodic random-mass harmonic matrix, this module derives
strict differentiability of every positive simple ordered frequency with
respect to two interior raw masses.  The proof uses the characteristic
equation and Mathlib's implicit-function theorem:

* the actual clipped matrix is smooth at every interior mass pair;
* a simple Hermitian eigenvalue is a simple characteristic root;
* continuity of the ordered spectrum identifies the implicit root branch
  with the same ordered eigenvalue.

Consequently the regular-patch theorem for the actual child-frequency chart
needs only simple positive modes and a nonzero actual Jacobian determinant.
No separate C1 premise remains.
-/

open scoped Matrix

namespace ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.HarmonicModes
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter Function Set

noncomputable section

/-- A finite matrix determinant is C1 at a parameter whenever every matrix
entry is C1 there. -/
theorem contDiffAt_one_det_of_entries
    {X index : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
    [Fintype index] [DecidableEq index]
    (matrix : X → Matrix index index Real) (x : X)
    (hmatrix : ∀ i j, ContDiffAt Real 1 (fun y => matrix y i j) x) :
    ContDiffAt Real 1 (fun y => (matrix y).det) x := by
  rw [show (fun y => (matrix y).det) =
      fun y => ∑ sigma : Equiv.Perm index,
        Equiv.Perm.sign sigma • ∏ i, matrix y (sigma i) i by
    funext y
    exact Matrix.det_apply (matrix y)]
  apply ContDiffAt.sum
  intro sigma _hsigma
  have hprod : ContDiffAt Real 1
      (fun y => ∏ i, matrix y (sigma i) i) x := by
    apply contDiffAt_prod
    intro i _hi
    exact hmatrix (sigma i) i
  exact hprod.const_smul (Equiv.Perm.sign sigma)

/-- Inside the iid support square, each actual varied mass coordinate is C1;
clipping is locally the identity. -/
theorem contDiffAt_one_twoSiteMassConfig_mass_of_mem_interior
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (i : Lattice.Site N) :
    ContDiffAt Real 1
      (fun nearby => (twoSiteMassConfig fixed site₁ site₂ nearby).mass i)
      pair := by
  have hnearSupport : ∀ᶠ nearby in nhds pair,
      nearby ∈ iidMassPairSupport := by
    filter_upwards [isOpen_interior.mem_nhds hpair] with nearby hnearby
    exact interior_subset hnearby
  by_cases hi₁ : i = site₁
  · subst i
    apply contDiffAt_fst.congr_of_eventuallyEq
    filter_upwards [hnearSupport] with nearby hnearby
    exact twoSiteMassConfig_mass_site₁_of_mem_support
      fixed site₁ site₂ hnearby
  · by_cases hi₂ : i = site₂
    · subst i
      apply contDiffAt_snd.congr_of_eventuallyEq
      filter_upwards [hnearSupport] with nearby hnearby
      exact twoSiteMassConfig_mass_site₂_of_mem_support
        fixed hsite hnearby
    · simpa [twoSiteMassConfig, hi₁, hi₂] using
        (contDiffAt_const :
          ContDiffAt Real 1
            (fun _ : Real × Real => fixed.mass i) pair)

/-- Every entry of the genuine mass-weighted bond matrix is C1 at an
interior two-mass pair. -/
theorem contDiffAt_one_twoSiteBondMatrix_apply_of_mem_interior
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (i j : Lattice.Site N) :
    ContDiffAt Real 1
      (fun nearby => twoSiteBondMatrix fixed site₁ site₂ nearby i j)
      pair := by
  unfold twoSiteBondMatrix massWeightedDifferenceMatrix
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  apply ContDiffAt.sum
  intro k _hk
  by_cases hkj : k = j
  · subst k
    simp only [ite_true]
    have hmass :=
      contDiffAt_one_twoSiteMassConfig_mass_of_mem_interior
        fixed hsite hpair j
    have hsqrt : ContDiffAt Real 1
        (fun nearby =>
          Real.sqrt ((twoSiteMassConfig fixed site₁ site₂ nearby).mass j))
        pair :=
      hmass.sqrt
        (ne_of_gt ((twoSiteMassConfig fixed site₁ site₂ pair).mass_pos j))
    exact contDiffAt_const.mul
      (hsqrt.inv
        (Real.sqrt_ne_zero'.2
          ((twoSiteMassConfig fixed site₁ site₂ pair).mass_pos j)))
  · simpa [hkj] using
      (contDiffAt_const :
        ContDiffAt Real 1 (fun _ : Real × Real => (0 : Real)) pair)

/-- Every entry of the actual harmonic matrix is C1 at an interior mass pair. -/
theorem contDiffAt_one_twoSiteHarmonicMatrix_apply_of_mem_interior
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (i j : Lattice.Site N) :
    ContDiffAt Real 1
      (fun nearby =>
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby).1 i j)
      pair := by
  unfold twoSiteHarmonicHermitian harmonicHermitian
    massWeightedHarmonicMatrix
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro k _hk
  exact
    (contDiffAt_one_twoSiteBondMatrix_apply_of_mem_interior
      fixed hsite hpair k i).mul
      (contDiffAt_one_twoSiteBondMatrix_apply_of_mem_interior
        fixed hsite hpair k j)

/-- The actual two-mass characteristic equation. -/
def actualTwoMassCharacteristicEquation
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (parameterEnergy : (Real × Real) × Real) : Real :=
  (Matrix.charpoly (twoSiteHarmonicHermitian
    fixed site₁ site₂ parameterEnergy.1).1).eval
      parameterEnergy.2

/-- The actual characteristic equation is C1 jointly in the two raw masses
and the spectral energy at every interior mass pair. -/
theorem contDiffAt_one_actualTwoMassCharacteristicEquation
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (energy : Real) :
    ContDiffAt Real 1
      (actualTwoMassCharacteristicEquation fixed site₁ site₂)
      (pair, energy) := by
  rw [show actualTwoMassCharacteristicEquation fixed site₁ site₂ =
      fun parameterEnergy =>
        ((Matrix.scalar (Lattice.Site N) parameterEnergy.2 :
            Matrix (Lattice.Site N) (Lattice.Site N) Real) -
          Matrix.of ((twoSiteHarmonicHermitian
            fixed site₁ site₂ parameterEnergy.1).val)).det by
    funext parameterEnergy
    exact Matrix.eval_charpoly _ _]
  refine contDiffAt_one_det_of_entries
    (matrix := fun parameterEnergy : (Real × Real) × Real =>
      (Matrix.scalar (Lattice.Site N) parameterEnergy.2 :
          Matrix (Lattice.Site N) (Lattice.Site N) Real) -
        Matrix.of ((twoSiteHarmonicHermitian
          fixed site₁ site₂ parameterEnergy.1).val))
    (x := (pair, energy)) ?_
  intro i j
  simp only [Matrix.sub_apply, Matrix.scalar_apply]
  have hmatrix :
      ContDiffAt Real 1
        (fun parameterEnergy : (Real × Real) × Real =>
          (twoSiteHarmonicHermitian
            fixed site₁ site₂ parameterEnergy.1).1 i j)
        (pair, energy) :=
    (contDiffAt_one_twoSiteHarmonicMatrix_apply_of_mem_interior
      fixed hsite hpair i j).fst'
  by_cases hij : i = j
  · subst j
    simpa [Matrix.diagonal_apply] using
      (contDiffAt_snd.sub hmatrix)
  · simpa [Matrix.diagonal_apply, hij] using hmatrix.neg

/-- At a simple Hermitian spectrum, every ordered eigenvalue is a simple
root of the characteristic polynomial. -/
theorem charpoly_derivative_eval_orderedEigenvalue_ne_zero
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card index)) :
    (Matrix.charpoly A.1).derivative.eval (orderedEigenvalue A k) ≠ 0 := by
  let lambda := orderedEigenvalue A k
  have hroot : (Matrix.charpoly A.1).IsRoot lambda := by
    exact charpoly_eval_orderedEigenvalue_eq_zero A k
  have hrootsNodup : (Matrix.charpoly A.1).roots.Nodup := by
    rw [A.2.roots_charpoly_eq_eigenvalues₀]
    change (Multiset.map A.2.eigenvalues₀ Finset.univ.val).Nodup
    apply Finset.univ.nodup.map
    intro i j hij
    exact hsimple hij
  have hmultLe :
      (Matrix.charpoly A.1).rootMultiplicity lambda ≤ 1 := by
    have hcount :=
      (Multiset.nodup_iff_count_le_one.mp hrootsNodup) lambda
    rwa [Polynomial.count_roots] at hcount
  intro hderivative
  have hp : (Matrix.charpoly A.1) ≠ 0 :=
    (Matrix.charpoly_monic A.1).ne_zero
  have hmultiple : 1 < (Matrix.charpoly A.1).rootMultiplicity lambda :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).2
      ⟨hroot, hderivative⟩
  omega

/-- Every actual ordered eigenvalue has a strict Fréchet derivative with
respect to the two raw masses at an interior simple-spectrum pair. -/
theorem exists_hasStrictFDerivAt_actualTwoMassOrderedEigenvalue
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple :
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (k : Fin (Fintype.card (Lattice.Site N))) :
    ∃ derivative : (Real × Real) →L[Real] Real,
      HasStrictFDerivAt
        (fun nearby =>
          orderedEigenvalue
            (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) k)
        derivative pair := by
  let A := twoSiteHarmonicHermitian fixed site₁ site₂ pair
  let lambda := orderedEigenvalue A k
  let characteristic :=
    actualTwoMassCharacteristicEquation fixed site₁ site₂
  let Dcharacteristic :=
    fderiv Real characteristic (pair, lambda)
  have hcharacteristicC1 :
      ContDiffAt Real 1 characteristic (pair, lambda) := by
    exact contDiffAt_one_actualTwoMassCharacteristicEquation
      fixed hsite hpair lambda
  have hcharacteristicDeriv :
      HasFDerivAt characteristic Dcharacteristic (pair, lambda) := by
    exact hcharacteristicC1.differentiableAt_one.hasFDerivAt
  have hcharacteristicStrict :
      HasStrictFDerivAt characteristic Dcharacteristic (pair, lambda) :=
    hcharacteristicC1.hasStrictFDerivAt'
      hcharacteristicDeriv (by norm_num)
  have hinclusion :
      HasFDerivAt (fun energy : Real => (pair, energy))
        (ContinuousLinearMap.inr Real (Real × Real) Real) lambda := by
    exact hasFDerivAt_prodMk_right pair lambda
  have hslice :
      HasFDerivAt (fun energy : Real => characteristic (pair, energy))
        (Dcharacteristic ∘L
          ContinuousLinearMap.inr Real (Real × Real) Real) lambda := by
    simpa [Function.comp_def] using
      hcharacteristicDeriv.comp lambda hinclusion
  have hpolynomial :
      HasFDerivAt (fun energy : Real => characteristic (pair, energy))
        (ContinuousLinearMap.toSpanSingleton Real
          ((Matrix.charpoly A.1).derivative.eval lambda)) lambda := by
    simpa [characteristic, actualTwoMassCharacteristicEquation, A, lambda] using
      ((Matrix.charpoly A.1).hasDerivAt lambda).hasFDerivAt
  have hpartial :
      Dcharacteristic ∘L
          ContinuousLinearMap.inr Real (Real × Real) Real =
        ContinuousLinearMap.toSpanSingleton Real
          ((Matrix.charpoly A.1).derivative.eval lambda) :=
    hslice.unique hpolynomial
  have hrootDerivative :
      (Matrix.charpoly A.1).derivative.eval lambda ≠ 0 :=
    charpoly_derivative_eval_orderedEigenvalue_ne_zero A hsimple k
  let scalarEquiv : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 ((Matrix.charpoly A.1).derivative.eval lambda) hrootDerivative)
  have hscalarEquiv :
      (scalarEquiv : Real →L[Real] Real) =
        ContinuousLinearMap.toSpanSingleton Real
          ((Matrix.charpoly A.1).derivative.eval lambda) := by
    apply ContinuousLinearMap.ext
    intro x
    simp [scalarEquiv, mul_comm]
  have hpartialInvertible :
      (Dcharacteristic ∘L
        ContinuousLinearMap.inr Real (Real × Real) Real).IsInvertible := by
    rw [hpartial]
    exact ⟨scalarEquiv, hscalarEquiv⟩
  let branch :=
    hcharacteristicStrict.implicitFunctionOfProdDomain
      hpartialInvertible
  have hbranchDerivative :
      HasStrictFDerivAt branch
        (-(Dcharacteristic ∘L
              ContinuousLinearMap.inr Real (Real × Real) Real).inverse ∘L
          (Dcharacteristic ∘L
            ContinuousLinearMap.inl Real (Real × Real) Real)) pair := by
    exact
      hcharacteristicStrict.hasStrictFDerivAt_implicitFunctionOfProdDomain
        hpartialInvertible
  let orderedBranch : Real × Real → Real :=
    fun nearby =>
      orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) k
  have horderedContinuous : Continuous orderedBranch :=
    (continuous_orderedEigenvalue k).comp
      (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)
  have horderedTendsto :
      Tendsto (fun nearby => (nearby, orderedBranch nearby))
        (nhds pair) (nhds (pair, lambda)) := by
    exact tendsto_id.prodMk_nhds horderedContinuous.continuousAt
  have hrootBase : characteristic (pair, lambda) = 0 := by
    exact charpoly_eval_orderedEigenvalue_eq_zero A k
  have hbranchEq : branch =ᶠ[nhds pair] orderedBranch := by
    have hiff :=
      hcharacteristicStrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hpartialInvertible
    filter_upwards [horderedTendsto.eventually hiff] with nearby hnearby
    have hrootNearby :
        characteristic (nearby, orderedBranch nearby) = 0 := by
      exact charpoly_eval_orderedEigenvalue_eq_zero
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) k
    exact (hnearby.mp (hrootNearby.trans hrootBase.symm))
  refine ⟨
    -(Dcharacteristic ∘L
          ContinuousLinearMap.inr Real (Real × Real) Real).inverse ∘L
      (Dcharacteristic ∘L
        ContinuousLinearMap.inl Real (Real × Real) Real), ?_⟩
  exact hbranchDerivative.congr_of_eventuallyEq hbranchEq


/-- One actual positive ordered frequency has a strict Fréchet derivative
with respect to the two raw masses at an interior simple-spectrum pair. -/
theorem exists_hasStrictFDerivAt_actualTwoMassOrderedModeFrequency
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple :
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (k : Fin (Fintype.card (Lattice.Site N)))
    (hpositive : 0 <
      orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair) k) :
    ∃ derivative : (Real × Real) →L[Real] Real,
      HasStrictFDerivAt
        (fun nearby =>
          orderedModeFrequency
            (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) k)
        derivative pair := by
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassOrderedEigenvalue
      fixed hsite hpair hsimple k
  refine ⟨
    (1 / (2 * Real.sqrt
      (orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair) k))) •
      derivative, ?_⟩
  simpa [orderedModeFrequency] using
    hderivative.sqrt (ne_of_gt hpositive)

end

end ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
