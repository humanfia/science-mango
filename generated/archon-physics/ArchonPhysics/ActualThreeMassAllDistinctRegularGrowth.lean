import ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeBudget
import ArchonPhysics.CubicVertexInfraredBound
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Explicit regular-budget growth for the actual all-distinct chart

The basis-free ordered collision weight vanishes at projector degeneracies.
On its nonzero branch it is the ordinary physical cubic vertex, so the
acoustic vertex estimate applies without assuming a globally simple
spectrum.  Together with the frozen mass band this gives one explicit,
volume-independent ceiling for every actual all-distinct tuple weight.

The final arithmetic lemma records the resulting finite-volume growth of a
single injective good chart at a uniform determinant threshold.  It does not
bound the number of injective patches needed to cover a determinant level.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.CubicVertexInfraredBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModeCoupling
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Set
open scoped ENNReal Matrix

noncomputable section

/-- The basis-free ordered cubic weight obeys the physical acoustic bound on
every positive tuple.  At a repeated eigenvalue at least one totalized
projector is zero, so the inequality remains true without a simple-spectrum
hypothesis. -/
theorem harmonicOrderedNormalizedInteractionWeight_three_le
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N)
    (hpositive : IsPositiveOrderedTriple mass modes) :
    harmonicOrderedNormalizedInteractionWeight mass modes ≤
      orderedModeFrequency (harmonicHermitian mass) (modes 0) *
        orderedModeFrequency (harmonicHermitian mass) (modes 1) *
          orderedModeFrequency (harmonicHermitian mass) (modes 2) / 8 := by
  classical
  let physicalModes : Fin 3 → Lattice.Site N := fun r =>
    orderedIndexEquiv (modes r)
  have hphysical : PositiveModeTuple mass physicalModes :=
    (isPositiveOrderedTriple_iff_physical mass modes).1 hpositive
  by_cases hall : ∀ r, orderedModeProjector (harmonicHermitian mass) (modes r) =
      Matrix.vecMulVec
        ⇑((harmonicHermitian mass).2.eigenvectorBasis
          (orderedIndexEquiv (modes r)))
        ⇑((harmonicHermitian mass).2.eigenvectorBasis
          (orderedIndexEquiv (modes r)))
  · have hkernel (r : Fin 3) (j l : Lattice.Site N) :
        projectedBondKernel (massWeightedDifferenceMatrix mass)
            (harmonicHermitian mass) (modes r) j l =
          (massWeightedDifferenceMatrix mass *ᵥ ⇑(
              (harmonicHermitian mass).2.eigenvectorBasis
                (orderedIndexEquiv (modes r)))) j *
            (massWeightedDifferenceMatrix mass *ᵥ ⇑(
              (harmonicHermitian mass).2.eigenvectorBasis
                (orderedIndexEquiv (modes r)))) l := by
      unfold projectedBondKernel
      rw [hall r, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
        Matrix.vecMul_transpose]
      rfl
    have hsquareEigen : orderedInteractionWeightSq
        (massWeightedDifferenceMatrix mass) (harmonicHermitian mass) modes =
          (∑ j, ∏ r,
            (massWeightedDifferenceMatrix mass *ᵥ ⇑(
              (harmonicHermitian mass).2.eigenvectorBasis
                (orderedIndexEquiv (modes r)))) j) ^ 2 := by
      unfold orderedInteractionWeightSq
      simp_rw [hkernel]
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _hl
      rw [← Finset.prod_mul_distrib]
    have hsquare : harmonicOrderedInteractionWeightSq mass modes =
        (interactionTensor mass 3 physicalModes) ^ 2 := by
      rw [harmonicOrderedInteractionWeightSq, hsquareEigen]
      congr 1
    have hacoustic := normalizedInteractionWeight_three_le
      mass physicalModes hphysical
    unfold harmonicOrderedNormalizedInteractionWeight
    rw [hsquare]
    simpa [physicalModes, normalizedInteractionWeight,
      orderedModeFrequency_harmonicHermitian_eq] using hacoustic
  · have hexists : ∃ r, orderedModeProjector
        (harmonicHermitian mass) (modes r) ≠
      Matrix.vecMulVec
        ⇑((harmonicHermitian mass).2.eigenvectorBasis
          (orderedIndexEquiv (modes r)))
        ⇑((harmonicHermitian mass).2.eigenvectorBasis
          (orderedIndexEquiv (modes r))) := by
      simpa only [not_forall] using hall
    obtain ⟨r, hr⟩ := hexists
    have hzero : orderedModeProjector
        (harmonicHermitian mass) (modes r) = 0 := by
      rcases orderedModeProjector_eq_zero_or_vecMulVec
          (harmonicHermitian mass) (modes r) with hz | houter
      · exact hz
      · exact (hr houter).elim
    have hkernel (j l : Lattice.Site N) :
        projectedBondKernel (massWeightedDifferenceMatrix mass)
          (harmonicHermitian mass) (modes r) j l = 0 := by
      simp [projectedBondKernel, hzero]
    have hproduct (j l : Lattice.Site N) :
        (∏ s, projectedBondKernel (massWeightedDifferenceMatrix mass)
          (harmonicHermitian mass) (modes s) j l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) (hkernel j l)
    have hweightZero :
        harmonicOrderedNormalizedInteractionWeight mass modes = 0 := by
      unfold harmonicOrderedNormalizedInteractionWeight
        harmonicOrderedInteractionWeightSq orderedInteractionWeightSq
      simp_rw [hproduct]
      simp
    rw [hweightZero]
    have hfrequencyNonneg (s : Fin 3) : 0 ≤
        orderedModeFrequency (harmonicHermitian mass) (modes s) :=
      Real.sqrt_nonneg _
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (hfrequencyNonneg 0) (hfrequencyNonneg 1))
        (hfrequencyNonneg 2))
      (by norm_num)

/-- Replacing any three physical masses by clipped coordinates preserves the
frozen iid support at every lattice site. -/
theorem threeMassSiteConfig_mass_mem_support
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple) :
    ∀ site, (threeMassSiteConfig fixed site₀ site₁ site₂ triple).mass site ∈
      massSupport := by
  intro site
  change (if site = site₀ then clippedMass triple.1.1
    else if site = site₁ then clippedMass triple.1.2
    else if site = site₂ then clippedMass triple.2
    else fixed.mass site) ∈ massSupport
  split_ifs
  · exact clippedMass_mem_support _
  · exact clippedMass_mem_support _
  · exact clippedMass_mem_support _
  · exact hfixed site

/-- Every ordered frequency in the actual three-mass family is bounded by the
frozen band edge `sqrt 5`, pointwise in all raw mass parameters. -/
theorem actualThreeMass_orderedModeFrequency_le_sqrt_five
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple)
    (mode : OrderedModeIndex N) :
    orderedModeFrequency
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple) mode ≤
      Real.sqrt 5 := by
  let mass := threeMassSiteConfig fixed site₀ site₁ site₂ triple
  have hmassLower : ∀ site, massLower ≤ mass.mass site := fun site =>
    (threeMassSiteConfig_mass_mem_support
      fixed hfixed site₀ site₁ site₂ triple site).1
  have hband := orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
    mass massLower massLower_pos hmassLower mode
  simpa [mass, threeMassHarmonicHermitian, massLower] using hband

/-- A realization- and volume-independent ceiling for every genuine
all-distinct conditional tuple weight. -/
theorem actualThreeMassAllDistinctTupleWeight_le_acousticCeiling
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (triple : MassTriple) :
    actualThreeMassAllDistinctTupleWeight
        fixed site₀ site₁ site₂ modes triple ≤
      ENNReal.ofReal
        (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) := by
  classical
  unfold actualThreeMassAllDistinctTupleWeight
  split_ifs with hdistinct
  · change (if hpositive : IsPositiveOrderedTriple
        (threeMassSiteConfig fixed site₀ site₁ site₂ triple) modes then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight
        (threeMassSiteConfig fixed site₀ site₁ site₂ triple) modes)
    else 0) ≤ _
    split_ifs with hpositive
    · apply ENNReal.ofReal_le_ofReal
      have hvertex := harmonicOrderedNormalizedInteractionWeight_three_le
        (threeMassSiteConfig fixed site₀ site₁ site₂ triple)
        modes hpositive
      have hfrequency (r : Fin 3) :
          orderedModeFrequency
              (threeMassHarmonicHermitian
                fixed site₀ site₁ site₂ triple) (modes r) ≤
            Real.sqrt 5 :=
        actualThreeMass_orderedModeFrequency_le_sqrt_five
          fixed hfixed site₀ site₁ site₂ triple (modes r)
      have hnonneg (r : Fin 3) : 0 ≤ orderedModeFrequency
          (threeMassHarmonicHermitian
            fixed site₀ site₁ site₂ triple) (modes r) :=
        Real.sqrt_nonneg _
      have hproduct :
          orderedModeFrequency
                (threeMassHarmonicHermitian
                  fixed site₀ site₁ site₂ triple) (modes 0) *
              orderedModeFrequency
                (threeMassHarmonicHermitian
                  fixed site₀ site₁ site₂ triple) (modes 1) *
              orderedModeFrequency
                (threeMassHarmonicHermitian
                  fixed site₀ site₁ site₂ triple) (modes 2) ≤
            Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 := by
        exact mul_le_mul
          (mul_le_mul (hfrequency 0) (hfrequency 1)
            (hnonneg 1) (Real.sqrt_nonneg _))
          (hfrequency 2) (hnonneg 2)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      exact hvertex.trans
        (div_le_div_of_nonneg_right hproduct (by norm_num))
    · exact bot_le
  · exact bot_le

/-- There are exactly `N³` ordered three-mode tuples at volume `N`. -/
theorem card_orderedModeTriple_eq_cube
    (N : Nat) [NeZero N] :
    Fintype.card (OrderedModeTriple N) = N ^ 3 := by
  simp [OrderedModeTriple, OrderedModeIndex, Lattice.Site, pow_succ]

/-- At a uniform determinant threshold `delta`, the crude but explicit
single-chart regular budget is bounded by the number of ordered tuples times
the acoustic ceiling.  The identity is left in cardinal form so it can be
combined with either exact cardinal simplification or a sharper spectral
sum estimate. -/
theorem actualThreeMassRegularPerSiteBudget_acousticCeiling_eq
    {N : Nat} [NeZero N] (delta : Real) :
    actualThreeMassRegularPerSiteBudget
        (fun _ : OrderedModeTriple N => ENNReal.ofReal
          (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
        (fun _ => delta) =
      (N : ENNReal)⁻¹ *
        (Fintype.card (OrderedModeTriple N) : ENNReal) *
          (ENNReal.ofReal
            (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) * 27 *
              (ENNReal.ofReal delta)⁻¹) := by
  classical
  unfold actualThreeMassRegularPerSiteBudget
  rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]
  ring


/-- After simplifying the ordered-mode cardinal, the crude single-chart
regular cost grows exactly quadratically in the volume at fixed `delta`. -/
theorem actualThreeMassRegularPerSiteBudget_acousticCeiling_eq_quadratic
    {N : Nat} [NeZero N] (delta : Real) :
    actualThreeMassRegularPerSiteBudget
        (fun _ : OrderedModeTriple N => ENNReal.ofReal
          (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
        (fun _ => delta) =
      (N : ENNReal) ^ 2 *
        (ENNReal.ofReal
          (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) * 27 *
            (ENNReal.ofReal delta)⁻¹) := by
  rw [actualThreeMassRegularPerSiteBudget_acousticCeiling_eq,
    card_orderedModeTriple_eq_cube]
  simp only [Nat.cast_pow]
  have hNzero : (N : ENNReal) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  have hNtop : (N : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  let coefficient : ENNReal :=
    ENNReal.ofReal
        (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) * 27 *
      (ENNReal.ofReal delta)⁻¹
  change (N : ENNReal)⁻¹ * (N : ENNReal) ^ 3 * coefficient =
    (N : ENNReal) ^ 2 * coefficient
  calc
    (N : ENNReal)⁻¹ * (N : ENNReal) ^ 3 * coefficient =
        ((N : ENNReal)⁻¹ * (N : ENNReal)) *
          (N : ENNReal) ^ 2 * coefficient := by ring
    _ = (N : ENNReal) ^ 2 * coefficient := by
      rw [ENNReal.inv_mul_cancel hNzero hNtop, one_mul]
end

end ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
