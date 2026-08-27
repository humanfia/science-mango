import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.NormDet
import ArchonPhysics.LocalCollisionMarkContinuity
import ArchonPhysics.TwoParameterSpectralAveragingAtlas

/-!
# Actual two-mass spectral charts for the periodic random-mass chain

This file puts the abstract two-parameter spectral atlas on the genuine
finite periodic random-mass model. Two distinct physical masses are varied,
all other masses are frozen, and the chart coordinates are two ordered
harmonic frequencies of the actual mass-weighted harmonic matrix.

The construction is total because the two raw coordinates are clipped to the
frozen iid support. On the iid support square clipping is exactly the
identity, so these are the two physical raw masses averaged by the iid law.

The deterministic conclusions proved here are:

* continuity of the actual bond matrix, harmonic Hermitian matrix and every
  two-mode frequency chart;
* local persistence of simple ordered spectrum;
* the actual projector-defined three-wave vertex/mark on this same family;
* an inverse-function-theorem patch inside the iid support whenever the
  Fréchet Jacobian of the actual frequency chart is nondegenerate.

The follow-up strict-derivative module discharges chart differentiability at
simple positive modes.  Nonvanishing of the actual two-dimensional Jacobian
determinant is the remaining model calculation.
-/

open scoped Matrix

namespace ArchonPhysics.ActualTwoMassSpectralChart

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter Function Set

noncomputable section

/-- Replace two physical masses by two clipped iid raw coordinates, leaving
every other mass equal to the fixed realization. -/
def twoSiteMassConfig {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real) :
    Lattice.PositiveMassConfig N where
  mass i :=
    if i = site₁ then clippedMass pair.1
    else if i = site₂ then clippedMass pair.2
    else fixed.mass i
  mass_pos i := by
    split_ifs
    · exact clippedMass_pos pair.1
    · exact clippedMass_pos pair.2
    · exact fixed.mass_pos i

@[simp] theorem twoSiteMassConfig_mass_site₁
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real) :
    (twoSiteMassConfig fixed site₁ site₂ pair).mass site₁ =
      clippedMass pair.1 := by
  simp [twoSiteMassConfig]

@[simp] theorem twoSiteMassConfig_mass_site₂
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (pair : Real × Real) :
    (twoSiteMassConfig fixed site₁ site₂ pair).mass site₂ =
      clippedMass pair.2 := by
  simp [twoSiteMassConfig, hsite.symm]

/-- On the support of the two iid raw masses, the first varied mass is the
raw first coordinate, not merely its clipped representative. -/
theorem twoSiteMassConfig_mass_site₁_of_mem_support
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) {pair : Real × Real}
    (hpair : pair ∈ iidMassPairSupport) :
    (twoSiteMassConfig fixed site₁ site₂ pair).mass site₁ = pair.1 := by
  rw [twoSiteMassConfig_mass_site₁, clippedMass_eq_self hpair.1]

/-- On the support square the second varied mass is exactly the second raw
iid coordinate. -/
theorem twoSiteMassConfig_mass_site₂_of_mem_support
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport) :
    (twoSiteMassConfig fixed site₁ site₂ pair).mass site₂ = pair.2 := by
  rw [twoSiteMassConfig_mass_site₂ fixed hsite,
    clippedMass_eq_self hpair.2]

/-- Every individual mass coordinate in the actual two-site family is a
continuous function of the two raw mass parameters. -/
theorem continuous_twoSiteMassConfig_mass
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ i : Lattice.Site N) :
    Continuous fun pair : Real × Real =>
      (twoSiteMassConfig fixed site₁ site₂ pair).mass i := by
  by_cases hi₁ : i = site₁
  · subst i
    simp only [twoSiteMassConfig_mass_site₁]
    unfold clippedMass
    fun_prop
  · by_cases hi₂ : i = site₂
    · subst i
      change Continuous fun pair : Real × Real =>
        if site₂ = site₁ then clippedMass pair.1
        else if site₂ = site₂ then clippedMass pair.2
        else fixed.mass site₂
      simp only [if_neg hi₁, eq_self, if_true]
      unfold clippedMass
      fun_prop
    · simpa [twoSiteMassConfig, hi₁, hi₂] using
        (continuous_const :
          Continuous fun _ : Real × Real => fixed.mass i)

/-- The genuine mass-weighted difference/bond matrix for the two varied
masses. -/
def twoSiteBondMatrix {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real) :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  massWeightedDifferenceMatrix (twoSiteMassConfig fixed site₁ site₂ pair)

/-- The genuine physical mass-weighted harmonic Hermitian matrix for the two
varied masses. -/
def twoSiteHarmonicHermitian {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real) :
    HermitianMatrix (Lattice.Site N) :=
  harmonicHermitian (twoSiteMassConfig fixed site₁ site₂ pair)

/-- Every entry of the actual two-mass bond matrix is continuous. -/
theorem continuous_twoSiteBondMatrix_apply
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ i j : Lattice.Site N) :
    Continuous fun pair : Real × Real =>
      twoSiteBondMatrix fixed site₁ site₂ pair i j := by
  unfold twoSiteBondMatrix massWeightedDifferenceMatrix
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  apply continuous_finsetSum Finset.univ
  intro k _hk
  by_cases hkj : k = j
  · subst k
    simp only [ite_true]
    exact continuous_const.mul
      ((Real.continuous_sqrt.comp
        (continuous_twoSiteMassConfig_mass fixed site₁ site₂ j)).inv₀
          (fun pair =>
            Real.sqrt_ne_zero'.2
              ((twoSiteMassConfig fixed site₁ site₂ pair).mass_pos j)))
  · simpa [hkj] using
      (continuous_const : Continuous fun _ : Real × Real => (0 : Real))

/-- Matrix-valued continuity of the actual mass-weighted difference matrix. -/
theorem continuous_twoSiteBondMatrix
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) :
    Continuous (twoSiteBondMatrix fixed site₁ site₂) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_twoSiteBondMatrix_apply fixed site₁ site₂ i j

/-- The actual two-mass harmonic Hermitian matrix depends continuously on the
two raw mass parameters. -/
theorem continuous_twoSiteHarmonicHermitian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) :
    Continuous (twoSiteHarmonicHermitian fixed site₁ site₂) := by
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
    (continuous_twoSiteBondMatrix_apply fixed site₁ site₂ k i).mul
      (continuous_twoSiteBondMatrix_apply fixed site₁ site₂ k j)

/-- The actual child-frequency chart obtained by selecting two ordered
physical harmonic modes. -/
def actualTwoMassChildFrequencyChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (child₁ child₂ :
      Fin (Fintype.card (Lattice.Site N))) (pair : Real × Real) :
    Real × Real :=
  (orderedModeFrequency (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
      child₁,
    orderedModeFrequency (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
      child₂)

/-- Every actual two-mode frequency chart is globally continuous (including
at spectral collisions and at the boundary introduced by clipping). -/
theorem continuous_actualTwoMassChildFrequencyChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N))) :
    Continuous
      (actualTwoMassChildFrequencyChart fixed site₁ site₂ child₁ child₂) := by
  exact
    ((continuous_orderedModeFrequency child₁).comp
      (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)).prodMk
      ((continuous_orderedModeFrequency child₂).comp
        (continuous_twoSiteHarmonicHermitian fixed site₁ site₂))

/-- A simple ordered spectrum of the actual two-mass matrix persists
throughout a neighborhood of the base mass pair. -/
theorem eventually_simple_twoSiteHarmonicHermitian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (pair : Real × Real)
    (hsimple :
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)) :
    ∀ᶠ nearby in nhds pair,
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) := by
  unfold SimpleOrderedSpectrum
  change ∀ᶠ nearby in nhds pair, ∀ i j,
    orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) i =
      orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) j →
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
            (twoSiteHarmonicHermitian fixed site₁ site₂ pair) i ≠
          orderedEigenvalue
            (twoSiteHarmonicHermitian fixed site₁ site₂ pair) j :=
      hsimple.ne hij
    have hi : ContinuousAt
        (fun nearby =>
          orderedEigenvalue
            (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) i) pair :=
      ((continuous_orderedEigenvalue i).comp
        (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)).continuousAt
    have hj : ContinuousAt
        (fun nearby =>
          orderedEigenvalue
            (twoSiteHarmonicHermitian fixed site₁ site₂ nearby) j) pair :=
      ((continuous_orderedEigenvalue j).comp
        (continuous_twoSiteHarmonicHermitian fixed site₁ site₂)).continuousAt
    filter_upwards [(hi.ne_iff_eventually_ne hj).1 hne] with nearby hnear
    exact fun heq => (hnear heq).elim

/-- The actual projector-defined collision mark of a fixed ordered mode
tuple along the two-mass family. -/
def actualTwoMassCollisionMark
    {N n : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (sign : Fin n → ModalPhaseMismatch.InteractionSign)
    (modes : Fin n → Fin (Fintype.card (Lattice.Site N)))
    (pair : Real × Real) : Real × Real :=
  orderedCollisionMark
    (twoSiteBondMatrix fixed site₁ site₂ pair)
    (twoSiteHarmonicHermitian fixed site₁ site₂ pair) sign modes


/-- The true Fréchet Jacobian of the selected pair of physical ordered
frequencies with respect to the two raw masses. -/
def actualTwoMassChildFrequencyJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N)))
    (pair : Real × Real) :
    (Real × Real) →L[Real] (Real × Real) :=
  fderiv Real
    (actualTwoMassChildFrequencyChart fixed site₁ site₂ child₁ child₂)
    pair

/-- A nonzero determinant of the actual two-mass frequency Jacobian produces
an open, measurable, differentiable and injective atlas patch contained in
the iid mass-support square.

This is the model-facing inverse-function-theorem bridge required by the
two-parameter atlas. Its hypotheses mention the actual physical
ordered-frequency map, rather than an abstract chart. -/
theorem exists_actualTwoMassChildFrequency_regularPatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (_hsite : site₁ ≠ site₂)
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N)))
    (pair : Real × Real) (hpair : pair ∈ interior iidMassPairSupport)
    (hC1 : ContDiffAt Real 1
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ child₁ child₂) pair)
    (hJacobian :
      (actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ child₁ child₂ pair).det ≠ 0) :
    ∃ patch : Set (Real × Real),
      pair ∈ patch ∧
      IsOpen patch ∧
      MeasurableSet patch ∧
      patch ⊆ iidMassPairSupport ∧
      DifferentiableOn Real
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂) patch ∧
      InjOn
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ child₁ child₂) patch := by
  let chart :=
    actualTwoMassChildFrequencyChart fixed site₁ site₂ child₁ child₂
  let J : (Real × Real) →L[Real] (Real × Real) :=
    actualTwoMassChildFrequencyJacobian
      fixed site₁ site₂ child₁ child₂ pair
  have hdetLinear : LinearMap.det J.toLinearMap ≠ 0 := by
    simpa [ContinuousLinearMap.det] using hJacobian
  have hker : J.ker = ⊥ := by
    by_contra hne
    exact hdetLinear
      (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hinjective : Function.Injective J :=
    LinearMap.ker_eq_bot.mp hker
  have hsurjective : Function.Surjective J :=
    LinearMap.injective_iff_surjective.mp hinjective
  have hrange : J.range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  let Jequiv : (Real × Real) ≃L[Real] (Real × Real) :=
    ContinuousLinearEquiv.ofBijective J hker hrange
  have hJequiv :
      (Jequiv : (Real × Real) →L[Real] (Real × Real)) = J := by
    exact ContinuousLinearEquiv.coe_ofBijective J hker hrange
  have hderiv : HasFDerivAt chart
      (Jequiv : (Real × Real) →L[Real] (Real × Real)) pair := by
    rw [hJequiv]
    simpa [chart, J, actualTwoMassChildFrequencyJacobian] using
      hC1.differentiableAt_one.hasFDerivAt
  let localChart : OpenPartialHomeomorph (Real × Real) (Real × Real) :=
    hC1.toOpenPartialHomeomorph chart hderiv (by norm_num)
  have hpairSource : pair ∈ localChart.source := by
    exact hC1.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  obtain ⟨regularitySet, hregularityNhds, hregularity⟩ :=
    hC1.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨regularityOpen, hopenSubset, hopen, hpairOpen⟩ :=
    mem_nhds_iff.mp hregularityNhds
  let patch : Set (Real × Real) :=
    localChart.source ∩ regularityOpen ∩ interior iidMassPairSupport
  refine ⟨patch, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨hpairSource, hpairOpen⟩, hpair⟩
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

end ArchonPhysics.ActualTwoMassSpectralChart
