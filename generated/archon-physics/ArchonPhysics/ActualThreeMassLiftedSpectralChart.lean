import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.NormDet
import ArchonPhysics.ActualTwoMassSpectralChart
import ArchonPhysics.ThreeParameterSpectralAveragingDensity

/-!
# Actual three-mass lifted spectral charts

Three distinct physical masses are varied in the genuine periodic
random-mass harmonic matrix.  The target coordinates are the two child
frequencies and the signed three-wave mismatch.  This supplies exactly the
third transverse parameter missing from a two-child-frequency chart.

This file proves continuity and the inverse-function patch theorem for the
true model.  The accompanying differentiability module discharges the C1
hypothesis at interior simple-positive configurations.
-/

open scoped Matrix

namespace ArchonPhysics.ActualThreeMassLiftedSpectralChart

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function Set

noncomputable section

/-- Replace three distinct physical masses by three clipped iid raw
coordinates and leave the remaining environment frozen. -/
def threeMassSiteConfig {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple) :
    Lattice.PositiveMassConfig N where
  mass i :=
    if i = site₀ then clippedMass triple.1.1
    else if i = site₁ then clippedMass triple.1.2
    else if i = site₂ then clippedMass triple.2
    else fixed.mass i
  mass_pos i := by
    split_ifs
    · exact clippedMass_pos triple.1.1
    · exact clippedMass_pos triple.1.2
    · exact clippedMass_pos triple.2
    · exact fixed.mass_pos i

@[simp] theorem threeMassSiteConfig_mass_site₀
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple) :
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass site₀ =
      clippedMass triple.1.1 := by
  simp [threeMassSiteConfig]

@[simp] theorem threeMassSiteConfig_mass_site₁
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N} (h₁₀ : site₁ ≠ site₀)
    (triple : MassTriple) :
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass site₁ =
      clippedMass triple.1.2 := by
  simp [threeMassSiteConfig, h₁₀]

@[simp] theorem threeMassSiteConfig_mass_site₂
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₂₀ : site₂ ≠ site₀) (h₂₁ : site₂ ≠ site₁)
    (triple : MassTriple) :
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass site₂ =
      clippedMass triple.2 := by
  simp [threeMassSiteConfig, h₂₀, h₂₁]

theorem threeMassSiteConfig_mass_site₀_of_mem_support
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) {triple : MassTriple}
    (htriple : triple ∈ iidMassTripleSupport) :
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass site₀ =
      triple.1.1 := by
  rw [threeMassSiteConfig_mass_site₀, clippedMass_eq_self htriple.1.1]

theorem threeMassSiteConfig_mass_site₁_of_mem_support
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N} (h₁₀ : site₁ ≠ site₀)
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport) :
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass site₁ =
      triple.1.2 := by
  rw [threeMassSiteConfig_mass_site₁ fixed h₁₀,
    clippedMass_eq_self htriple.1.2]

theorem threeMassSiteConfig_mass_site₂_of_mem_support
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₂₀ : site₂ ≠ site₀) (h₂₁ : site₂ ≠ site₁)
    {triple : MassTriple} (htriple : triple ∈ iidMassTripleSupport) :
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass site₂ =
      triple.2 := by
  rw [threeMassSiteConfig_mass_site₂ fixed h₂₀ h₂₁,
    clippedMass_eq_self htriple.2]

/-- Every physical mass coordinate in the three-parameter family is
continuous. -/
theorem continuous_threeMassSiteConfig_mass
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ i : Lattice.Site N) :
    Continuous fun triple : MassTriple =>
      (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass i := by
  by_cases hi₀ : i = site₀
  · subst i
    simp only [threeMassSiteConfig_mass_site₀]
    unfold clippedMass
    fun_prop
  · by_cases hi₁ : i = site₁
    · subst i
      change Continuous fun triple : MassTriple =>
        if site₁ = site₀ then clippedMass triple.1.1
        else if site₁ = site₁ then clippedMass triple.1.2
        else if site₁ = site₂ then clippedMass triple.2
        else fixed.mass site₁
      simp [hi₀]
      unfold clippedMass
      fun_prop
    · by_cases hi₂ : i = site₂
      · subst i
        change Continuous fun triple : MassTriple =>
          if site₂ = site₀ then clippedMass triple.1.1
          else if site₂ = site₁ then clippedMass triple.1.2
          else if site₂ = site₂ then clippedMass triple.2
          else fixed.mass site₂
        simp [hi₀, hi₁]
        unfold clippedMass
        fun_prop
      · simpa [threeMassSiteConfig, hi₀, hi₁, hi₂] using
          (continuous_const : Continuous fun _ : MassTriple => fixed.mass i)

def threeMassBondMatrix {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple) :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  massWeightedDifferenceMatrix
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple)

def threeMassHarmonicHermitian {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple) :
    HermitianMatrix (Lattice.Site N) :=
  harmonicHermitian
    (threeMassSiteConfig fixed site₀ site₁ site₂ triple)

theorem continuous_threeMassBondMatrix_apply
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ i j : Lattice.Site N) :
    Continuous fun triple : MassTriple =>
      threeMassBondMatrix fixed site₀ site₁ site₂ triple i j := by
  unfold threeMassBondMatrix massWeightedDifferenceMatrix
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  apply continuous_finsetSum Finset.univ
  intro k _hk
  by_cases hkj : k = j
  · subst k
    simp only [ite_true]
    exact continuous_const.mul
      ((Real.continuous_sqrt.comp
        (continuous_threeMassSiteConfig_mass
          fixed site₀ site₁ site₂ j)).inv₀
          (fun triple => Real.sqrt_ne_zero'.2
            ((threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass_pos j)))
  · simpa [hkj] using
      (continuous_const : Continuous fun _ : MassTriple => (0 : Real))

theorem continuous_threeMassHarmonicHermitian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) :
    Continuous (threeMassHarmonicHermitian fixed site₀ site₁ site₂) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold massWeightedHarmonicMatrix
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply continuous_finsetSum Finset.univ
  intro k _hk
  exact
    (continuous_threeMassBondMatrix_apply fixed site₀ site₁ site₂ k i).mul
      (continuous_threeMassBondMatrix_apply fixed site₀ site₁ site₂ k j)

/-- The actual three-dimensional observable `(child₁, child₂,
mismatch)`. -/
def actualThreeMassLiftedFrequencyChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : MassTriple :=
  let A := threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple
  ((orderedModeFrequency A (modes 1), orderedModeFrequency A (modes 2)),
    ∑ r, (sign r).coefficient * orderedModeFrequency A (modes r))

theorem continuous_actualThreeMassLiftedFrequencyChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    Continuous (actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes) := by
  let hfrequency (r : Fin 3) : Continuous fun triple : MassTriple =>
      orderedModeFrequency
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r) :=
    (continuous_orderedModeFrequency (modes r)).comp
      (continuous_threeMassHarmonicHermitian fixed site₀ site₁ site₂)
  unfold actualThreeMassLiftedFrequencyChart
  exact ((hfrequency 1).prodMk (hfrequency 2)).prodMk
    (continuous_finsetSum Finset.univ fun r _hr =>
      continuous_const.mul (hfrequency r))

theorem eventually_simple_threeMassHarmonicHermitian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)) :
    ∀ᶠ nearby in nhds triple, SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) := by
  unfold SimpleOrderedSpectrum
  change ∀ᶠ nearby in nhds triple, ∀ i j,
    orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) i =
      orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) j →
      i = j
  rw [eventually_all]
  intro i
  rw [eventually_all]
  intro j
  by_cases hij : i = j
  · subst j
    exact Filter.Eventually.of_forall fun _ _ => rfl
  · have hne :
        orderedEigenvalue
            (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple) i ≠
          orderedEigenvalue
            (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple) j :=
      hsimple.ne hij
    have hi : ContinuousAt (fun nearby => orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) i) triple :=
      ((continuous_orderedEigenvalue i).comp
        (continuous_threeMassHarmonicHermitian
          fixed site₀ site₁ site₂)).continuousAt
    have hj : ContinuousAt (fun nearby => orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby) j) triple :=
      ((continuous_orderedEigenvalue j).comp
        (continuous_threeMassHarmonicHermitian
          fixed site₀ site₁ site₂)).continuousAt
    filter_upwards [(hi.ne_iff_eventually_ne hj).1 hne] with nearby hnear
    exact fun heq => (hnear heq).elim

/-- True Frechet Jacobian of the actual lifted chart. -/
def actualThreeMassLiftedFrequencyJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : MassTriple →L[Real] MassTriple :=
  fderiv Real
    (actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes) triple

/-- A nonzero actual lifted Jacobian produces an open injective patch inside
the three-mass iid support. -/
theorem exists_actualThreeMassLiftedFrequency_regularPatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) (htriple : triple ∈ interior iidMassTripleSupport)
    (hC1 : ContDiffAt Real 1
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) triple)
    (hJacobian :
      (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det ≠ 0) :
    ∃ patch : Set MassTriple,
      triple ∈ patch ∧ IsOpen patch ∧ MeasurableSet patch ∧
      patch ⊆ iidMassTripleSupport ∧
      DifferentiableOn Real
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes) patch ∧
      InjOn
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes) patch := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  let J : MassTriple →L[Real] MassTriple :=
    actualThreeMassLiftedFrequencyJacobian
      fixed site₀ site₁ site₂ sign modes triple
  have hdetLinear : LinearMap.det J.toLinearMap ≠ 0 := by
    simpa [ContinuousLinearMap.det] using hJacobian
  have hker : J.ker = ⊥ := by
    by_contra hne
    exact hdetLinear (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hinjective : Function.Injective J := LinearMap.ker_eq_bot.mp hker
  have hsurjective : Function.Surjective J :=
    LinearMap.injective_iff_surjective.mp hinjective
  have hrange : J.range = ⊤ := LinearMap.range_eq_top.mpr hsurjective
  let Jequiv : MassTriple ≃L[Real] MassTriple :=
    ContinuousLinearEquiv.ofBijective J hker hrange
  have hJequiv : (Jequiv : MassTriple →L[Real] MassTriple) = J :=
    ContinuousLinearEquiv.coe_ofBijective J hker hrange
  have hderiv : HasFDerivAt chart
      (Jequiv : MassTriple →L[Real] MassTriple) triple := by
    rw [hJequiv]
    simpa [chart, J, actualThreeMassLiftedFrequencyJacobian] using
      hC1.differentiableAt_one.hasFDerivAt
  let localChart : OpenPartialHomeomorph MassTriple MassTriple :=
    hC1.toOpenPartialHomeomorph chart hderiv (by norm_num)
  have htripleSource : triple ∈ localChart.source :=
    hC1.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  obtain ⟨regularitySet, hregularityNhds, hregularity⟩ :=
    hC1.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨regularityOpen, hopenSubset, hopen, htripleOpen⟩ :=
    mem_nhds_iff.mp hregularityNhds
  let patch : Set MassTriple :=
    localChart.source ∩ regularityOpen ∩ interior iidMassTripleSupport
  refine ⟨patch, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨htripleSource, htripleOpen⟩, htriple⟩
  · exact (localChart.open_source.inter hopen).inter isOpen_interior
  · exact ((localChart.open_source.inter hopen).inter
      isOpen_interior).measurableSet
  · intro nearby hnearby
    exact interior_subset hnearby.2
  · apply (hregularity.mono ?_).differentiableOn (by norm_num)
    intro nearby hnearby
    exact hopenSubset hnearby.1.2
  · apply localChart.injOn.mono
    intro nearby hnearby
    exact hnearby.1.1

end

end ArchonPhysics.ActualThreeMassLiftedSpectralChart
