import ArchonPhysics.ActualThreeMassProjectorWeightJacobian
import ArchonPhysics.OrderedEigenvalueHellmannFeynman

/-!
# Actual three-mass Hellmann--Feynman Jacobian

This module identifies the genuine raw-mass derivative of the periodic
random-mass harmonic spectrum with the dual-cycle spectral-projector
weights.  For three selected sites it proves the exact determinant reduction

`lifted frequency Jacobian ≠ 0 ↔ projector-weight minor ≠ 0`.

This is only the differential/coarea input for the all-distinct collision
sector.  It does not assert that the projector minor is pointwise nonzero:
paired reflection-symmetric masses inside the physical support give genuine
rank-degenerate simple-spectrum points.  A later argument must establish an
almost-everywhere or resonance-restricted separation statement.  Nor does
this Jacobian identity by itself imply collision-network rigidity, kernel
coercivity, or relaxation to equipartition.
-/


open scoped Matrix

namespace ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedJacobianFactorization
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedEigenvalueHellmannFeynman
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open Filter Set

noncomputable section

def actualMassCoordinateInjection :
    Fin 3 → Real →L[Real] MassTriple :=
  ![(ContinuousLinearMap.inl Real (Real × Real) Real) ∘L
      (ContinuousLinearMap.inl Real Real Real),
    (ContinuousLinearMap.inl Real (Real × Real) Real) ∘L
      (ContinuousLinearMap.inr Real Real Real),
    ContinuousLinearMap.inr Real (Real × Real) Real]

@[simp] theorem actualMassCoordinateInjection_one (s : Fin 3) :
    actualMassCoordinateInjection s 1 = massTripleBasis s := by
  fin_cases s <;> simp [actualMassCoordinateInjection]
  ext <;> simp

def actualMassCoordinateLine
    (triple : MassTriple) (s : Fin 3) (t : Real) : MassTriple :=
  actualMassCoordinateInjection s t + triple

@[simp] theorem actualMassCoordinateLine_zero
    (triple : MassTriple) (s : Fin 3) :
    actualMassCoordinateLine triple s 0 = triple := by
  simp [actualMassCoordinateLine]

theorem hasFDerivAt_actualMassCoordinateLine
    (triple : MassTriple) (s : Fin 3) :
    HasFDerivAt (actualMassCoordinateLine triple s)
      (actualMassCoordinateInjection s) 0 :=
  (actualMassCoordinateInjection s).hasFDerivAt.add_const triple

theorem hasDerivAt_comp_actualMassCoordinateLine
    {f : MassTriple → Real} {derivative : MassTriple →L[Real] Real}
    {triple : MassTriple} (h : HasFDerivAt f derivative triple)
    (s : Fin 3) :
    HasDerivAt
      (fun t => f (actualMassCoordinateLine triple s t))
      (derivative (massTripleBasis s)) 0 := by
  have hbase : HasFDerivAt f derivative
      (actualMassCoordinateLine triple s 0) := by
    simpa using h
  have hcomp := hbase.comp 0
    (hasFDerivAt_actualMassCoordinateLine triple s)
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using
    hcomp.hasDerivAt

@[simp] theorem actualThreeMassRawCoordinate_line_same
    (triple : MassTriple) (s : Fin 3) (t : Real) :
    actualThreeMassRawCoordinate (actualMassCoordinateLine triple s t) s =
      actualThreeMassRawCoordinate triple s + t := by
  fin_cases s <;> simp [actualMassCoordinateLine,
    actualMassCoordinateInjection, actualThreeMassRawCoordinate,
    add_comm]

theorem actualThreeMassRawCoordinate_line_off
    (triple : MassTriple) {s q : Fin 3} (hqs : q ≠ s) (t : Real) :
    actualThreeMassRawCoordinate (actualMassCoordinateLine triple s t) q =
      actualThreeMassRawCoordinate triple q := by
  fin_cases s <;> fin_cases q <;>
    simp_all [actualMassCoordinateLine, actualMassCoordinateInjection,
      actualThreeMassRawCoordinate]

theorem eventually_actualMassCoordinateLine_mem_support
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport) (s : Fin 3) :
    ∀ᶠ t in nhds 0,
      actualMassCoordinateLine triple s t ∈ iidMassTripleSupport := by
  have htendsto :=
    (hasFDerivAt_actualMassCoordinateLine triple s).continuousAt
  change Tendsto (actualMassCoordinateLine triple s) (nhds 0)
    (nhds (actualMassCoordinateLine triple s 0)) at htendsto
  rw [actualMassCoordinateLine_zero triple s] at htendsto
  exact (htendsto.eventually (isOpen_interior.mem_nhds htriple)).mono
    (fun _ ht => interior_subset ht)

theorem eventually_actualThreeMass_selected_mass
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport) (s : Fin 3) :
    ∀ᶠ t in nhds 0,
      (threeMassSiteConfig fixed site₀ site₁ site₂
        (actualMassCoordinateLine triple s t)).mass
          (actualThreeMassSelectedSite site₀ site₁ site₂ s) =
        actualThreeMassRawCoordinate triple s + t := by
  filter_upwards
    [eventually_actualMassCoordinateLine_mem_support htriple s] with t ht
  fin_cases s
  · simpa [actualThreeMassSelectedSite, actualMassCoordinateLine,
      actualMassCoordinateInjection, actualThreeMassRawCoordinate, add_comm] using
      threeMassSiteConfig_mass_site₀_of_mem_support
        fixed site₀ site₁ site₂ ht
  · simpa [actualThreeMassSelectedSite, actualMassCoordinateLine,
      actualMassCoordinateInjection, actualThreeMassRawCoordinate, add_comm] using
      threeMassSiteConfig_mass_site₁_of_mem_support fixed h₁₀ ht
  · simpa [actualThreeMassSelectedSite, actualMassCoordinateLine,
      actualMassCoordinateInjection, actualThreeMassRawCoordinate, add_comm] using
      threeMassSiteConfig_mass_site₂_of_mem_support fixed h₂₀ h₂₁ ht

theorem eventually_actualThreeMass_mass_eq_off_selected
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (s : Fin 3) (i : Lattice.Site N)
    (hi : i ≠ actualThreeMassSelectedSite site₀ site₁ site₂ s) :
    ∀ᶠ t in nhds 0,
      (threeMassSiteConfig fixed site₀ site₁ site₂
        (actualMassCoordinateLine triple s t)).mass i =
      (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass i := by
  have hbase : triple ∈ iidMassTripleSupport := interior_subset htriple
  filter_upwards
    [eventually_actualMassCoordinateLine_mem_support htriple s] with t ht
  fin_cases s
  · have hi₀ : i ≠ site₀ := by
      simpa [actualThreeMassSelectedSite] using hi
    by_cases hi₁ : i = site₁
    · subst i
      rw [threeMassSiteConfig_mass_site₁_of_mem_support fixed h₁₀ ht,
        threeMassSiteConfig_mass_site₁_of_mem_support fixed h₁₀ hbase]
      simp [actualMassCoordinateLine, actualMassCoordinateInjection]
    · by_cases hi₂ : i = site₂
      · subst i
        rw [threeMassSiteConfig_mass_site₂_of_mem_support fixed h₂₀ h₂₁ ht,
          threeMassSiteConfig_mass_site₂_of_mem_support fixed h₂₀ h₂₁ hbase]
        simp [actualMassCoordinateLine, actualMassCoordinateInjection]
      · simp [threeMassSiteConfig, hi₀, hi₁, hi₂]
  · have hi₁ : i ≠ site₁ := by
      simpa [actualThreeMassSelectedSite] using hi
    by_cases hi₀ : i = site₀
    · subst i
      rw [threeMassSiteConfig_mass_site₀_of_mem_support
          fixed site₀ site₁ site₂ ht,
        threeMassSiteConfig_mass_site₀_of_mem_support
          fixed site₀ site₁ site₂ hbase]
      simp [actualMassCoordinateLine, actualMassCoordinateInjection]
    · by_cases hi₂ : i = site₂
      · subst i
        rw [threeMassSiteConfig_mass_site₂_of_mem_support fixed h₂₀ h₂₁ ht,
          threeMassSiteConfig_mass_site₂_of_mem_support fixed h₂₀ h₂₁ hbase]
        simp [actualMassCoordinateLine, actualMassCoordinateInjection]
      · simp [threeMassSiteConfig, hi₀, hi₁, hi₂]
  · have hi₂ : i ≠ site₂ := by
      simpa [actualThreeMassSelectedSite] using hi
    by_cases hi₀ : i = site₀
    · subst i
      rw [threeMassSiteConfig_mass_site₀_of_mem_support
          fixed site₀ site₁ site₂ ht,
        threeMassSiteConfig_mass_site₀_of_mem_support
          fixed site₀ site₁ site₂ hbase]
      simp [actualMassCoordinateLine, actualMassCoordinateInjection]
    · by_cases hi₁ : i = site₁
      · subst i
        rw [threeMassSiteConfig_mass_site₁_of_mem_support fixed h₁₀ ht,
          threeMassSiteConfig_mass_site₁_of_mem_support fixed h₁₀ hbase]
        simp [actualMassCoordinateLine, actualMassCoordinateInjection]
      · simp [threeMassSiteConfig, hi₀, hi₁, hi₂]

theorem actualThreeMass_selected_mass_base
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport)
    (s : Fin 3) :
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass
        (actualThreeMassSelectedSite site₀ site₁ site₂ s) =
      actualThreeMassRawCoordinate triple s := by
  fin_cases s
  · simpa [actualThreeMassSelectedSite, actualThreeMassRawCoordinate] using
      threeMassSiteConfig_mass_site₀_of_mem_support
        fixed site₀ site₁ site₂ htriple
  · simpa [actualThreeMassSelectedSite, actualThreeMassRawCoordinate] using
      threeMassSiteConfig_mass_site₁_of_mem_support fixed h₁₀ htriple
  · simpa [actualThreeMassSelectedSite, actualThreeMassRawCoordinate] using
      threeMassSiteConfig_mass_site₂_of_mem_support fixed h₂₀ h₂₁ htriple

def actualMassCoordinateProjection :
    Fin 3 → MassTriple →L[Real] Real :=
  ![massTripleCoordinateZero, massTripleCoordinateOne,
    massTripleCoordinateTwo]

@[simp] theorem actualMassCoordinateProjection_apply
    (s : Fin 3) (triple : MassTriple) :
    actualMassCoordinateProjection s triple =
      actualThreeMassRawCoordinate triple s := by
  fin_cases s <;> simp [actualMassCoordinateProjection,
    massTripleCoordinateZero, massTripleCoordinateOne,
    massTripleCoordinateTwo, actualThreeMassRawCoordinate]

@[simp] theorem actualMassCoordinateProjection_basis_self
    (s : Fin 3) :
    actualMassCoordinateProjection s (massTripleBasis s) = 1 := by
  fin_cases s <;> simp [actualMassCoordinateProjection,
    massTripleCoordinateZero, massTripleCoordinateOne,
    massTripleCoordinateTwo]

@[simp] theorem actualThreeMassRawCoordinate_massTripleBasis_self
    (s : Fin 3) :
    actualThreeMassRawCoordinate (massTripleBasis s) s = 1 := by
  rw [← actualMassCoordinateProjection_apply]
  exact actualMassCoordinateProjection_basis_self s

theorem hasFDerivAt_inverse_actualThreeMassRawCoordinate
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport) (s : Fin 3) :
    HasFDerivAt
      (fun nearby => (actualThreeMassRawCoordinate nearby s)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton Real
          (-((actualThreeMassRawCoordinate triple s) ^ 2)⁻¹)) ∘L
        actualMassCoordinateProjection s) triple := by
  have hcoordinate : HasFDerivAt
      (fun nearby => actualThreeMassRawCoordinate nearby s)
      (actualMassCoordinateProjection s) triple := by
    have hfunction :
        (fun nearby => actualThreeMassRawCoordinate nearby s) =
          actualMassCoordinateProjection s := by
      funext nearby
      exact (actualMassCoordinateProjection_apply s nearby).symm
    rw [hfunction]
    exact (actualMassCoordinateProjection s).hasFDerivAt
  have hne := actualThreeMassRawCoordinate_ne_zero htriple s
  simpa only [Function.comp_def] using
    (hasFDerivAt_inv hne).comp triple hcoordinate

theorem hasDerivAt_actualThreeMassDualHermitian_apply
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (s : Fin 3) (i j : Lattice.Site N) :
    HasDerivAt
      (fun t =>
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂
          (actualMassCoordinateLine triple s t)).1 i j)
      ((actualThreeMassRawMassColumnScale triple s •
        Matrix.vecMulVec
          (actualThreeMassCycleDirection site₀ site₁ site₂ s)
          (actualThreeMassCycleDirection site₀ site₁ site₂ s)) i j) 0 := by
  let selected := actualThreeMassSelectedSite site₀ site₁ site₂ s
  let direction := actualThreeMassCycleDirection site₀ site₁ site₂ s
  let baseConfig :=
    threeMassSiteConfig fixed site₀ site₁ site₂ triple
  let movingConfig : Real → Lattice.PositiveMassConfig N := fun t =>
    threeMassSiteConfig fixed site₀ site₁ site₂
      (actualMassCoordinateLine triple s t)
  have hinverseRaw :=
    hasFDerivAt_inverse_actualThreeMassRawCoordinate htriple s
  have hinverseRawLine :=
    hasDerivAt_comp_actualMassCoordinateLine hinverseRaw s
  have hinverseMoving := hinverseRawLine.congr_of_eventuallyEq
    (f₁ := fun t => ((movingConfig t).mass selected)⁻¹)
    (by
      filter_upwards
        [eventually_actualThreeMass_selected_mass
          fixed h₁₀ h₂₀ h₂₁ htriple s] with t ht
      rw [ht, actualThreeMassRawCoordinate_line_same])
  have hoffEventually :
      ∀ᶠ t in nhds 0, ∀ q, q ≠ selected →
        (movingConfig t).mass q = baseConfig.mass q := by
    rw [eventually_all]
    intro q
    by_cases hq : q = selected
    · exact Filter.Eventually.of_forall fun _ hne =>
        (hne hq).elim
    · filter_upwards
        [eventually_actualThreeMass_mass_eq_off_selected
          fixed h₁₀ h₂₀ h₂₁ htriple s q hq] with t ht
      exact fun _ => ht
  have hmatrixEventually :
      (fun t =>
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂
          (actualMassCoordinateLine triple s t)).1 i j) =ᶠ[nhds 0]
      (fun t =>
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple).1 i j +
          (((movingConfig t).mass selected)⁻¹ -
            (baseConfig.mass selected)⁻¹) *
              (Matrix.vecMulVec direction direction) i j) := by
    filter_upwards [hoffEventually] with t hoff
    have hsub :=
      dualMassWeightedHarmonicMatrix_sub_eq_smul_rankOne_of_eq_off
        (movingConfig t) baseConfig selected hoff
    have hentry := congrArg
      (fun M : Matrix (Lattice.Site N) (Lattice.Site N) Real => M i j) hsub
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hentry
    change
      dualMassWeightedHarmonicMatrix (movingConfig t) i j =
        dualMassWeightedHarmonicMatrix baseConfig i j +
          (((movingConfig t).mass selected)⁻¹ -
            (baseConfig.mass selected)⁻¹) *
              (Matrix.vecMulVec direction direction) i j
    change
      dualMassWeightedHarmonicMatrix (movingConfig t) i j -
          dualMassWeightedHarmonicMatrix baseConfig i j =
        (((movingConfig t).mass selected)⁻¹ -
          (baseConfig.mass selected)⁻¹) *
            (Matrix.vecMulVec direction direction) i j at hentry
    linarith
  have hrhs :=
    (((hinverseMoving.sub_const (baseConfig.mass selected)⁻¹).mul_const
      ((Matrix.vecMulVec direction direction) i j)).const_add
        ((actualThreeMassDualHermitian
          fixed site₀ site₁ site₂ triple).1 i j))
  have hactual := hrhs.congr_of_eventuallyEq hmatrixEventually
  simpa [actualThreeMassRawMassColumnScale,
    ContinuousLinearMap.comp_apply,
    actualMassCoordinateProjection_basis_self,
    ContinuousLinearMap.toSpanSingleton_apply,
    actualThreeMassDualHermitian, direction, selected,
    Matrix.smul_apply, smul_eq_mul] using hactual

theorem orderedEigenvalue_actualThreeMass_eq_dual
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple) k =
      orderedEigenvalue
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple) k := by
  exact orderedEigenvalue_harmonic_eq_dual
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple) k

theorem simple_actualThreeMassDualHermitian_of_simple
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)) :
    SimpleOrderedSpectrum
      (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple) := by
  intro i j hij
  apply hsimple
  rw [orderedEigenvalue_actualThreeMass_eq_dual
      fixed site₀ site₁ site₂ triple i,
    orderedEigenvalue_actualThreeMass_eq_dual
      fixed site₀ site₁ site₂ triple j]
  exact hij

theorem eventually_simple_actualThreeMassDualHermitian_line
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (s : Fin 3) :
    ∀ᶠ t in nhds 0, SimpleOrderedSpectrum
      (actualThreeMassDualHermitian fixed site₀ site₁ site₂
        (actualMassCoordinateLine triple s t)) := by
  have htendsto :=
    (hasFDerivAt_actualMassCoordinateLine triple s).continuousAt
  change Tendsto (actualMassCoordinateLine triple s) (nhds 0)
    (nhds (actualMassCoordinateLine triple s 0)) at htendsto
  rw [actualMassCoordinateLine_zero triple s] at htendsto
  have hphysical := htendsto.eventually
    (eventually_simple_threeMassHarmonicHermitian
      fixed site₀ site₁ site₂ triple hsimple)
  exact hphysical.mono fun t hnearby =>
    simple_actualThreeMassDualHermitian_of_simple
      fixed site₀ site₁ site₂ (actualMassCoordinateLine triple s t) hnearby

theorem differentiableAt_orderedEigenvalue_actualThreeMassDual_line
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (s : Fin 3) (r : Fin (Fintype.card (Lattice.Site N))) :
    DifferentiableAt Real
      (fun t => orderedEigenvalue
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂
          (actualMassCoordinateLine triple s t)) r) 0 := by
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_actualThreeMassOrderedEigenvalue
      fixed h₁₀ h₂₀ h₂₁ htriple hsimple r
  have hphysicalLine :=
    hasDerivAt_comp_actualMassCoordinateLine
      hderivative.hasFDerivAt s
  have hdualLine : HasDerivAt
      (fun t => orderedEigenvalue
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂
          (actualMassCoordinateLine triple s t)) r)
      (derivative (massTripleBasis s)) 0 :=
    hphysicalLine.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t =>
        (orderedEigenvalue_actualThreeMass_eq_dual
          fixed site₀ site₁ site₂
            (actualMassCoordinateLine triple s t) r).symm)
  exact hdualLine.differentiableAt

theorem actualThreeMassDualEigenvalueDerivative_line_eq_projectorWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (s : Fin 3) (k : Fin (Fintype.card (Lattice.Site N)))
    (eigenvalueDerivative : Real)
    (heigenvalue : HasDerivAt
      (fun t => orderedEigenvalue
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂
          (actualMassCoordinateLine triple s t)) k)
      eigenvalueDerivative 0) :
    eigenvalueDerivative =
      actualThreeMassRawMassColumnScale triple s *
        (actualThreeMassCycleDirection site₀ site₁ site₂ s ⬝ᵥ
          (orderedModeProjector
            (actualThreeMassDualHermitian fixed site₀ site₁ site₂
              (actualMassCoordinateLine triple s 0)) k *ᵥ
            actualThreeMassCycleDirection site₀ site₁ site₂ s)) := by
  let dualSample : Real → HermitianMatrix (Lattice.Site N) := fun t =>
    actualThreeMassDualHermitian fixed site₀ site₁ site₂
      (actualMassCoordinateLine triple s t)
  have hsimpleDual : SimpleOrderedSpectrum (dualSample 0) := by
    simpa [dualSample] using simple_actualThreeMassDualHermitian_of_simple
      fixed site₀ site₁ site₂ triple hsimple
  have hsimpleDualEventually :
      ∀ᶠ t in nhds 0, SimpleOrderedSpectrum (dualSample t) := by
    simpa [dualSample] using
      eventually_simple_actualThreeMassDualHermitian_line
        fixed site₀ site₁ site₂ triple hsimple s
  have hdualEigenvalueDifferentiable :
      ∀ r, DifferentiableAt Real
        (fun t => orderedEigenvalue (dualSample t) r) 0 := by
    intro r
    simpa [dualSample] using
      differentiableAt_orderedEigenvalue_actualThreeMassDual_line
        fixed h₁₀ h₂₀ h₂₁ htriple hsimple s r
  exact orderedEigenvalueDerivative_eq_projectorWeight
    (sample := dualSample) (x := 0) (hsimple := hsimpleDual)
    (hsimpleEventually := hsimpleDualEventually)
    (c := actualThreeMassRawMassColumnScale triple s)
    (v := actualThreeMassCycleDirection site₀ site₁ site₂ s)
    (hmatrix := fun i j => by
      simpa [dualSample] using
        hasDerivAt_actualThreeMassDualHermitian_apply
          fixed h₁₀ h₂₀ h₂₁ htriple s i j)
    (heigenvalueDifferentiable := hdualEigenvalueDifferentiable)
    (k := k) (eigenvalueDerivative := eigenvalueDerivative)
    (heigenvalue := by simpa [dualSample] using heigenvalue)

theorem actualThreeMassDualEigenvalueDerivative_eq_projectorWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (s : Fin 3) (k : Fin (Fintype.card (Lattice.Site N)))
    (eigenvalueDerivative : Real)
    (heigenvalue : HasDerivAt
      (fun t => orderedEigenvalue
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂
          (actualMassCoordinateLine triple s t)) k)
      eigenvalueDerivative 0) :
    eigenvalueDerivative =
      actualThreeMassRawMassColumnScale triple s *
        (actualThreeMassCycleDirection site₀ site₁ site₂ s ⬝ᵥ
          (orderedModeProjector
            (actualThreeMassDualHermitian
              fixed site₀ site₁ site₂ triple) k *ᵥ
            actualThreeMassCycleDirection site₀ site₁ site₂ s)) := by
  simpa using
    actualThreeMassDualEigenvalueDerivative_line_eq_projectorWeight
      fixed h₁₀ h₂₀ h₂₁ htriple hsimple s k
        eigenvalueDerivative heigenvalue

theorem actualThreeMassOrderedEigenvalueDerivative_basis_eq_projectorWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (k : Fin (Fintype.card (Lattice.Site N)))
    (energyDerivative : MassTriple →L[Real] Real)
    (henergy : HasFDerivAt
      (fun nearby => orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) k)
      energyDerivative triple)
    (s : Fin 3) :
    energyDerivative (massTripleBasis s) =
      actualThreeMassRawMassColumnScale triple s *
        (actualThreeMassCycleDirection site₀ site₁ site₂ s ⬝ᵥ
          (orderedModeProjector
            (actualThreeMassDualHermitian
              fixed site₀ site₁ site₂ triple) k *ᵥ
            actualThreeMassCycleDirection site₀ site₁ site₂ s)) := by
  have henergyLine :=
    hasDerivAt_comp_actualMassCoordinateLine henergy s
  have hdualEnergyLine : HasDerivAt
      (fun t => orderedEigenvalue
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂
          (actualMassCoordinateLine triple s t)) k)
      (energyDerivative (massTripleBasis s)) 0 :=
    henergyLine.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t =>
        (orderedEigenvalue_actualThreeMass_eq_dual
          fixed site₀ site₁ site₂
            (actualMassCoordinateLine triple s t) k).symm)
  exact actualThreeMassDualEigenvalueDerivative_eq_projectorWeight
    fixed h₁₀ h₂₀ h₂₁ htriple hsimple s k
      (energyDerivative (massTripleBasis s)) hdualEnergyLine

@[simp] theorem massTripleLinearFunctional_massTripleBasis
    (a : Fin 3 → Real) (s : Fin 3) :
    massTripleLinearFunctional a (massTripleBasis s) = a s := by
  fin_cases s <;> simp

/-- The strict derivative of one actual positive ordered frequency is
exactly the corresponding row of the genuine scaled projector-weight
matrix.  This is an identity, not a nondegeneracy hypothesis. -/
theorem exists_actualThreeMassFrequencyDerivative_eq_projectorRow
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) (r : Fin 3) :
    ∃ derivative : MassTriple →L[Real] Real,
      HasStrictFDerivAt
        (fun nearby => orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
            (modes r)) derivative triple ∧
      derivative = massTripleLinearFunctional
        ((actualThreeMassFrequencyProjectorJacobianMatrix
          fixed site₀ site₁ site₂ modes triple) r) := by
  obtain ⟨energyDerivative, henergy⟩ :=
    exists_hasStrictFDerivAt_actualThreeMassOrderedEigenvalue
      fixed h₁₀ h₂₀ h₂₁ htriple hsimple (modes r)
  let derivative : MassTriple →L[Real] Real :=
    actualThreeMassFrequencyRowScale
      fixed site₀ site₁ site₂ modes triple r • energyDerivative
  have hfrequency : HasStrictFDerivAt
      (fun nearby => orderedModeFrequency
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
          (modes r)) derivative triple := by
    simpa [derivative, actualThreeMassFrequencyRowScale,
      orderedModeFrequency, one_div] using
        henergy.sqrt (ne_of_gt (hpositive r))
  refine ⟨derivative, hfrequency, ?_⟩
  apply ContinuousLinearMap.coe_injective
  apply massTripleBasis.ext
  intro s
  change actualThreeMassFrequencyRowScale
      fixed site₀ site₁ site₂ modes triple r *
        energyDerivative (massTripleBasis s) =
    massTripleLinearFunctional
      ((actualThreeMassFrequencyProjectorJacobianMatrix
        fixed site₀ site₁ site₂ modes triple) r) (massTripleBasis s)
  rw [massTripleLinearFunctional_massTripleBasis]
  rw [actualThreeMassOrderedEigenvalueDerivative_basis_eq_projectorWeight
    fixed h₁₀ h₂₀ h₂₁ htriple hsimple (modes r)
      energyDerivative henergy.hasFDerivAt s]
  simp only [actualThreeMassFrequencyProjectorJacobianMatrix,
    scaledOrderedProjectorWeightMatrix, rowColumnScaledMatrix,
    orderedProjectorWeightMatrix]
  ring

/-- Assemble the three exact strict frequency derivatives into the canonical
`MassTriple` endomorphism represented by the actual projector Jacobian
matrix. -/
theorem exists_actualThreeMassFrequencyDerivatives_eq_projectorJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    ∃ derivative : Fin 3 → MassTriple →L[Real] Real,
      (∀ r, HasStrictFDerivAt
        (fun nearby => orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
            (modes r)) (derivative r) triple) ∧
      frequencyTripleDerivative derivative =
        massTripleLinearMapOfMatrix
          (actualThreeMassFrequencyProjectorJacobianMatrix
            fixed site₀ site₁ site₂ modes triple) := by
  choose derivative hderivative hrow using fun r =>
    exists_actualThreeMassFrequencyDerivative_eq_projectorRow
      fixed h₁₀ h₂₀ h₂₁ modes htriple hsimple hpositive r
  refine ⟨derivative, hderivative, ?_⟩
  apply frequencyTripleDerivative_eq_massTripleLinearMapOfMatrix
  intro r x
  rw [hrow r]

/-- Exact actual-model reduction of the lifted chart Jacobian to the
dual-cycle projector-weight minor.  It deliberately makes no assertion that
the minor is nonzero: symmetry points inside the physical mass support can
make it vanish, so subsequent coarea arguments must prove only an
almost-everywhere or resonance-restricted separation statement. -/
theorem actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    (actualThreeMassLiftedFrequencyJacobian
      fixed site₀ site₁ site₂ sign modes triple).det ≠ 0 ↔
      (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det ≠ 0 := by
  obtain ⟨derivative, hderivative, hlifted⟩ :=
    exists_frequencyDerivatives_actualThreeMassLifted_det_ne_zero_iff
        fixed h₁₀ h₂₀ h₂₁ sign modes htriple hsimple hpositive
  obtain ⟨canonicalDerivative, hcanonical, hcanonicalMatrix⟩ :=
    exists_actualThreeMassFrequencyDerivatives_eq_projectorJacobian
      fixed h₁₀ h₂₀ h₂₁ modes htriple hsimple hpositive
  have hderivativeEq : derivative = canonicalDerivative := by
    funext r
    exact (hderivative r).hasFDerivAt.unique
      (hcanonical r).hasFDerivAt
  have hfrequencyMatrix :
      frequencyTripleDerivative derivative =
        massTripleLinearMapOfMatrix
          (actualThreeMassFrequencyProjectorJacobianMatrix
            fixed site₀ site₁ site₂ modes triple) := by
    rw [hderivativeEq]
    exact hcanonicalMatrix
  have hdet :
      (frequencyTripleDerivative derivative).det =
        (actualThreeMassFrequencyProjectorJacobianMatrix
          fixed site₀ site₁ site₂ modes triple).det := by
    rw [hfrequencyMatrix, det_massTripleLinearMapOfMatrix]
  calc
    (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det ≠ 0 ↔
        (frequencyTripleDerivative derivative).det ≠ 0 := hlifted
    _ ↔ (actualThreeMassFrequencyProjectorJacobianMatrix
        fixed site₀ site₁ site₂ modes triple).det ≠ 0 := by rw [hdet]
    _ ↔ (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det ≠ 0 :=
      actualThreeMassFrequencyProjectorJacobianMatrix_det_ne_zero_iff
        fixed site₀ site₁ site₂ modes htriple hpositive

end

end ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
