import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import ArchonPhysics.ActualThreeMassLiftedSpectralChart
import ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability

/-!
# Differentiability of actual three-mass lifted spectral charts

At an interior three-mass point with simple spectrum, each positive ordered
frequency is a strict differentiable branch of the genuine characteristic
equation.  Combining the three branches proves strict differentiability of
the actual `(child₁, child₂, mismatch)` chart.
-/

open scoped Matrix

namespace ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.HarmonicModes
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function Set

noncomputable section

/-- Inside the support interior, clipping is locally the identity in all
three varied coordinates. -/
theorem contDiffAt_one_threeMassSiteConfig_mass_of_mem_interior
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (i : Lattice.Site N) :
    ContDiffAt Real 1
      (fun nearby =>
        (threeMassSiteConfig fixed site₀ site₁ site₂ nearby).mass i)
      triple := by
  have hnearSupport : ∀ᶠ nearby in nhds triple,
      nearby ∈ iidMassTripleSupport := by
    filter_upwards [isOpen_interior.mem_nhds htriple] with nearby hnearby
    exact interior_subset hnearby
  by_cases hi₀ : i = site₀
  · subst i
    have hcoordinate : ContDiffAt Real 1
        (fun nearby : MassTriple => nearby.1.1) triple := by fun_prop
    apply hcoordinate.congr_of_eventuallyEq
    filter_upwards [hnearSupport] with nearby hnearby
    exact threeMassSiteConfig_mass_site₀_of_mem_support
      fixed site₀ site₁ site₂ hnearby
  · by_cases hi₁ : i = site₁
    · subst i
      have hcoordinate : ContDiffAt Real 1
          (fun nearby : MassTriple => nearby.1.2) triple := by fun_prop
      apply hcoordinate.congr_of_eventuallyEq
      filter_upwards [hnearSupport] with nearby hnearby
      exact threeMassSiteConfig_mass_site₁_of_mem_support
        fixed h₁₀ hnearby
    · by_cases hi₂ : i = site₂
      · subst i
        have hcoordinate : ContDiffAt Real 1
            (fun nearby : MassTriple => nearby.2) triple := by fun_prop
        apply hcoordinate.congr_of_eventuallyEq
        filter_upwards [hnearSupport] with nearby hnearby
        exact threeMassSiteConfig_mass_site₂_of_mem_support
          fixed h₂₀ h₂₁ hnearby
      · simpa [threeMassSiteConfig, hi₀, hi₁, hi₂] using
          (contDiffAt_const : ContDiffAt Real 1
            (fun _ : MassTriple => fixed.mass i) triple)

theorem contDiffAt_one_threeMassBondMatrix_apply_of_mem_interior
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (i j : Lattice.Site N) :
    ContDiffAt Real 1
      (fun nearby =>
        threeMassBondMatrix fixed site₀ site₁ site₂ nearby i j)
      triple := by
  unfold threeMassBondMatrix massWeightedDifferenceMatrix
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  apply ContDiffAt.sum
  intro k _hk
  by_cases hkj : k = j
  · subst k
    simp only [ite_true]
    have hmass :=
      contDiffAt_one_threeMassSiteConfig_mass_of_mem_interior
        fixed h₁₀ h₂₀ h₂₁ htriple j
    have hsqrt : ContDiffAt Real 1
        (fun nearby => Real.sqrt
          ((threeMassSiteConfig fixed site₀ site₁ site₂ nearby).mass j))
        triple :=
      hmass.sqrt (ne_of_gt
        ((threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass_pos j))
    exact contDiffAt_const.mul
      (hsqrt.inv (Real.sqrt_ne_zero'.2
        ((threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass_pos j)))
  · simpa [hkj] using
      (contDiffAt_const : ContDiffAt Real 1
        (fun _ : MassTriple => (0 : Real)) triple)

theorem contDiffAt_one_threeMassHarmonicMatrix_apply_of_mem_interior
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (i j : Lattice.Site N) :
    ContDiffAt Real 1
      (fun nearby =>
        (threeMassHarmonicHermitian
          fixed site₀ site₁ site₂ nearby).1 i j) triple := by
  unfold threeMassHarmonicHermitian harmonicHermitian
    massWeightedHarmonicMatrix
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro k _hk
  exact
    (contDiffAt_one_threeMassBondMatrix_apply_of_mem_interior
      fixed h₁₀ h₂₀ h₂₁ htriple k i).mul
      (contDiffAt_one_threeMassBondMatrix_apply_of_mem_interior
        fixed h₁₀ h₂₀ h₂₁ htriple k j)

/-- Characteristic equation jointly in the three raw masses and energy. -/
def actualThreeMassCharacteristicEquation
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (parameterEnergy : MassTriple × Real) : Real :=
  (Matrix.charpoly (threeMassHarmonicHermitian
    fixed site₀ site₁ site₂ parameterEnergy.1).1).eval
      parameterEnergy.2

theorem contDiffAt_one_actualThreeMassCharacteristicEquation
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (energy : Real) :
    ContDiffAt Real 1
      (actualThreeMassCharacteristicEquation fixed site₀ site₁ site₂)
      (triple, energy) := by
  rw [show actualThreeMassCharacteristicEquation fixed site₀ site₁ site₂ =
      fun parameterEnergy =>
        ((Matrix.scalar (Lattice.Site N) parameterEnergy.2 :
            Matrix (Lattice.Site N) (Lattice.Site N) Real) -
          Matrix.of ((threeMassHarmonicHermitian
            fixed site₀ site₁ site₂ parameterEnergy.1).val)).det by
    funext parameterEnergy
    exact Matrix.eval_charpoly _ _]
  refine contDiffAt_one_det_of_entries
    (matrix := fun parameterEnergy : MassTriple × Real =>
      (Matrix.scalar (Lattice.Site N) parameterEnergy.2 :
          Matrix (Lattice.Site N) (Lattice.Site N) Real) -
        Matrix.of ((threeMassHarmonicHermitian
          fixed site₀ site₁ site₂ parameterEnergy.1).val))
    (x := (triple, energy)) ?_
  intro i j
  simp only [Matrix.sub_apply, Matrix.scalar_apply]
  have hmatrix : ContDiffAt Real 1
      (fun parameterEnergy : MassTriple × Real =>
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂
          parameterEnergy.1).1 i j) (triple, energy) :=
    (contDiffAt_one_threeMassHarmonicMatrix_apply_of_mem_interior
      fixed h₁₀ h₂₀ h₂₁ htriple i j).fst'
  by_cases hij : i = j
  · subst j
    simpa [Matrix.diagonal_apply] using contDiffAt_snd.sub hmatrix
  · simpa [Matrix.diagonal_apply, hij] using hmatrix.neg

/-- Every actual ordered eigenvalue has a strict derivative with respect to
the three raw masses at an interior simple-spectrum point. -/
theorem exists_hasStrictFDerivAt_actualThreeMassOrderedEigenvalue
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (k : Fin (Fintype.card (Lattice.Site N))) :
    ∃ derivative : MassTriple →L[Real] Real,
      HasStrictFDerivAt
        (fun nearby => orderedEigenvalue
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) k)
        derivative triple := by
  let A := threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple
  let lambda := orderedEigenvalue A k
  let characteristic :=
    actualThreeMassCharacteristicEquation fixed site₀ site₁ site₂
  let Dcharacteristic := fderiv Real characteristic (triple, lambda)
  have hcharacteristicC1 :
      ContDiffAt Real 1 characteristic (triple, lambda) :=
    contDiffAt_one_actualThreeMassCharacteristicEquation
      fixed h₁₀ h₂₀ h₂₁ htriple lambda
  have hcharacteristicDeriv :
      HasFDerivAt characteristic Dcharacteristic (triple, lambda) :=
    hcharacteristicC1.differentiableAt_one.hasFDerivAt
  have hcharacteristicStrict :
      HasStrictFDerivAt characteristic Dcharacteristic (triple, lambda) :=
    hcharacteristicC1.hasStrictFDerivAt' hcharacteristicDeriv (by norm_num)
  have hinclusion : HasFDerivAt (fun energy : Real => (triple, energy))
      (ContinuousLinearMap.inr Real MassTriple Real) lambda :=
    hasFDerivAt_prodMk_right triple lambda
  have hslice : HasFDerivAt
      (fun energy : Real => characteristic (triple, energy))
      (Dcharacteristic ∘L ContinuousLinearMap.inr Real MassTriple Real) lambda := by
    simpa [Function.comp_def] using hcharacteristicDeriv.comp lambda hinclusion
  have hpolynomial : HasFDerivAt
      (fun energy : Real => characteristic (triple, energy))
      (ContinuousLinearMap.toSpanSingleton Real
        ((Matrix.charpoly A.1).derivative.eval lambda)) lambda := by
    simpa [characteristic, actualThreeMassCharacteristicEquation, A, lambda] using
      ((Matrix.charpoly A.1).hasDerivAt lambda).hasFDerivAt
  have hpartial :
      Dcharacteristic ∘L ContinuousLinearMap.inr Real MassTriple Real =
        ContinuousLinearMap.toSpanSingleton Real
          ((Matrix.charpoly A.1).derivative.eval lambda) :=
    hslice.unique hpolynomial
  have hrootDerivative :
      (Matrix.charpoly A.1).derivative.eval lambda ≠ 0 :=
    charpoly_derivative_eval_orderedEigenvalue_ne_zero A hsimple k
  let scalarEquiv : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 ((Matrix.charpoly A.1).derivative.eval lambda) hrootDerivative)
  have hscalarEquiv : (scalarEquiv : Real →L[Real] Real) =
      ContinuousLinearMap.toSpanSingleton Real
        ((Matrix.charpoly A.1).derivative.eval lambda) := by
    apply ContinuousLinearMap.ext
    intro x
    simp [scalarEquiv, mul_comm]
  have hpartialInvertible :
      (Dcharacteristic ∘L
        ContinuousLinearMap.inr Real MassTriple Real).IsInvertible := by
    rw [hpartial]
    exact ⟨scalarEquiv, hscalarEquiv⟩
  let branch := hcharacteristicStrict.implicitFunctionOfProdDomain
    hpartialInvertible
  have hbranchDerivative : HasStrictFDerivAt branch
      (-(Dcharacteristic ∘L
            ContinuousLinearMap.inr Real MassTriple Real).inverse ∘L
        (Dcharacteristic ∘L
          ContinuousLinearMap.inl Real MassTriple Real)) triple :=
    hcharacteristicStrict.hasStrictFDerivAt_implicitFunctionOfProdDomain
      hpartialInvertible
  let orderedBranch : MassTriple → Real := fun nearby =>
    orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) k
  have horderedContinuous : Continuous orderedBranch :=
    (continuous_orderedEigenvalue k).comp
      (continuous_threeMassHarmonicHermitian fixed site₀ site₁ site₂)
  have horderedTendsto : Tendsto (fun nearby => (nearby, orderedBranch nearby))
      (nhds triple) (nhds (triple, lambda)) :=
    tendsto_id.prodMk_nhds horderedContinuous.continuousAt
  have hrootBase : characteristic (triple, lambda) = 0 :=
    charpoly_eval_orderedEigenvalue_eq_zero A k
  have hbranchEq : branch =ᶠ[nhds triple] orderedBranch := by
    have hiff :=
      hcharacteristicStrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hpartialInvertible
    filter_upwards [horderedTendsto.eventually hiff] with nearby hnearby
    have hrootNearby : characteristic (nearby, orderedBranch nearby) = 0 :=
      charpoly_eval_orderedEigenvalue_eq_zero
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) k
    exact hnearby.mp (hrootNearby.trans hrootBase.symm)
  refine ⟨
    -(Dcharacteristic ∘L
          ContinuousLinearMap.inr Real MassTriple Real).inverse ∘L
      (Dcharacteristic ∘L
        ContinuousLinearMap.inl Real MassTriple Real), ?_⟩
  exact hbranchDerivative.congr_of_eventuallyEq hbranchEq

theorem exists_hasStrictFDerivAt_actualThreeMassOrderedModeFrequency
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (k : Fin (Fintype.card (Lattice.Site N)))
    (hpositive : 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple) k) :
    ∃ derivative : MassTriple →L[Real] Real,
      HasStrictFDerivAt
        (fun nearby => orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) k)
        derivative triple := by
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_actualThreeMassOrderedEigenvalue
      fixed h₁₀ h₂₀ h₂₁ htriple hsimple k
  refine ⟨(1 / (2 * Real.sqrt
    (orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple) k))) •
      derivative, ?_⟩
  simpa [orderedModeFrequency] using hderivative.sqrt (ne_of_gt hpositive)

/-- The complete actual child-child-mismatch chart has a strict derivative
at every interior simple-positive point. -/
theorem exists_hasStrictFDerivAt_actualThreeMassLiftedFrequencyChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    ∃ derivative : MassTriple →L[Real] MassTriple,
      HasStrictFDerivAt
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes) derivative triple := by
  choose derivative hderivative using fun r =>
    exists_hasStrictFDerivAt_actualThreeMassOrderedModeFrequency
      fixed h₁₀ h₂₀ h₂₁ htriple hsimple (modes r) (hpositive r)
  let mismatchDerivative : MassTriple →L[Real] Real :=
    ∑ r, (sign r).coefficient • derivative r
  have hmismatch : HasStrictFDerivAt
      (fun nearby => ∑ r, (sign r).coefficient *
        orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
          (modes r)) mismatchDerivative triple := by
    change HasStrictFDerivAt
      (∑ r, fun nearby : MassTriple => (sign r).coefficient *
        orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
          (modes r)) mismatchDerivative triple
    simpa only [mismatchDerivative] using
      HasStrictFDerivAt.sum (u := Finset.univ)
        (fun r _hr => (hderivative r).const_mul (sign r).coefficient)
  refine ⟨(derivative 1).prod (derivative 2) |>.prod mismatchDerivative, ?_⟩
  convert ((hderivative 1).prodMk (hderivative 2)).prodMk hmismatch using 1 <;>
    rfl

end

end ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
