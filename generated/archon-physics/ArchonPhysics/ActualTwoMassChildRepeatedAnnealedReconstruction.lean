import ArchonPhysics.ActualTwoMassChildRepeatedConditionalFubini
import ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
import ArchonPhysics.IIDMassPairFiniteVolumeReconstruction

/-!
# Full annealed reconstruction from an actual two-mass chart

Two selected iid masses and their finite complementary environment exactly
reconstruct the canonical annealed child-repeated reduced law.  Consequently
any conditional coarea estimate holding for every frozen environment
integrates to a valid annealed estimate.  No realization-wise estimate is
asserted.
-/

open scoped ENNReal

namespace ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedBridge
open ArchonPhysics.ActualTwoMassChildRepeatedConditionalFubini
open ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Every coordinate of the exact pair/complement reconstruction is
measurable on the product state space. -/
theorem measurable_finiteVolumePositiveMassPairReconstruction_mass
    {N : Nat} [NeZero N]
    (site₁ site₂ site : Lattice.Site N) :
    Measurable fun state :
        (Real × Real) ×
          FiniteMassVector (finiteVolumeMassPairComplement site₁ site₂) ↦
      (finiteVolumePositiveMassPairReconstruction site₁ site₂ state).mass
        site := by
  unfold finiteVolumePositiveMassPairReconstruction twoSiteMassConfig
  change Measurable fun state :
      (Real × Real) ×
        FiniteMassVector (finiteVolumeMassPairComplement site₁ site₂) ↦
    if site = site₁ then clippedMass state.1.1
    else if site = site₂ then clippedMass state.1.2
    else if hmem :
        site.val ∈ finiteVolumeMassPairComplement site₁ site₂ then
      clippedMass (state.2 ⟨site.val, hmem⟩)
    else massLower
  by_cases hsite₁ : site = site₁
  · simp only [hsite₁, if_true]
    exact measurable_clippedMass.comp
      (measurable_fst.comp measurable_fst)
  · simp only [hsite₁, if_false]
    by_cases hsite₂ : site = site₂
    · simp only [hsite₂, if_true]
      exact measurable_clippedMass.comp
        (measurable_snd.comp measurable_fst)
    · simp only [hsite₂, if_false]
      by_cases hmem :
          site.val ∈ finiteVolumeMassPairComplement site₁ site₂
      · simp only [dif_pos hmem]
        exact measurable_clippedMass.comp
          ((measurable_pi_apply
            (⟨site.val, hmem⟩ :
              finiteVolumeMassPairComplement site₁ site₂)).comp
                measurable_snd)
      · simp only [dif_neg hmem]
        exact measurable_const

/-- Evaluation of the pair-indexed child measure is measurable for every
measurable target whenever all mass coordinates are measurable. -/
theorem measurable_childRepeatedReducedPerSitePairMeasure_apply
    {S : Type*} [MeasurableSpace S]
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun state ↦ (massSample state).mass site)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    Measurable fun state ↦
      childRepeatedReducedPerSitePairMeasure (massSample state) A := by
  classical
  unfold childRepeatedReducedPerSitePairMeasure
  simp only [Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul]
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro modes _hmodes
  let triple := childRepeatedModeTriple modes
  have hmatrix : Measurable fun state ↦
      harmonicHermitian (massSample state) := by
    apply Measurable.subtype_mk
    exact
      MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
        massSample hmass
  have hfrequencies : Measurable fun state ↦ fun mode ↦
      orderedModeFrequency (harmonicHermitian (massSample state)) mode :=
    measurable_orderedModeFrequencies_unconditional
      (fun state ↦ harmonicHermitian (massSample state)) hmatrix
  have hpositive : MeasurableSet {state |
      IsPositiveOrderedTriple (massSample state) triple} := by
    rw [show {state |
        IsPositiveOrderedTriple (massSample state) triple} =
        ⋂ r, {state | 0 < orderedModeFrequency
          (harmonicHermitian (massSample state)) (triple r)} by
      ext state
      simp [IsPositiveOrderedTriple]]
    exact MeasurableSet.iInter fun r ↦
      measurableSet_lt measurable_const hfrequencies.eval
  have hweight : Measurable fun state ↦
      ENNReal.ofReal
        (harmonicOrderedNormalizedInteractionWeight
          (massSample state) triple) :=
    (measurable_harmonicOrderedNormalizedInteractionWeight
      massSample hmass triple).ennreal_ofReal
  have hpoint : Measurable fun state ↦
      childRepeatedReducedFrequencyPair (massSample state) modes := by
    exact hfrequencies.eval.prodMk hfrequencies.eval
  have hatom : Measurable fun state ↦
      (Measure.dirac
        (childRepeatedReducedFrequencyPair (massSample state) modes)) A := by
    exact (Measure.measurable_coe hA).comp
      (Measure.measurable_dirac.comp hpoint)
  let simple : S → ENNReal := fun state ↦
    if IsPositiveOrderedTriple (massSample state) triple then
      ENNReal.ofReal
          (harmonicOrderedNormalizedInteractionWeight
            (massSample state) triple) *
        (Measure.dirac
          (childRepeatedReducedFrequencyPair (massSample state) modes)) A
    else 0
  have hsimple : Measurable simple := by
    exact Measurable.ite hpositive (hweight.mul hatom)
      (measurable_const : Measurable fun _ : S ↦ (0 : ENNReal))
  have heq : (fun state ↦
      (if IsPositiveOrderedTriple (massSample state)
          (childRepeatedModeTriple modes) then
        ENNReal.ofReal
            (harmonicOrderedNormalizedInteractionWeight (massSample state)
              (childRepeatedModeTriple modes)) •
          Measure.dirac
            (childRepeatedReducedFrequencyPair (massSample state) modes)
      else 0) A) = simple := by
    funext state
    by_cases hstate : IsPositiveOrderedTriple (massSample state) triple
    · simp [simple, triple, hstate, Measure.smul_apply, smul_eq_mul]
    · simp [simple, triple, hstate]
  rw [heq]
  exact hsimple

/-- The frozen complementary environment always lies in the iid mass
support, including at the two harmless fallback coordinates. -/
theorem finitePairEnvironmentPositiveMassConfig_mass_mem_support
    {N : Nat} [NeZero N] (site₁ site₂ : Lattice.Site N)
    (rest : FiniteMassVector
      (finiteVolumeMassPairComplement site₁ site₂))
    (site : Lattice.Site N) :
    (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest).mass site ∈
      massSupport := by
  unfold finitePairEnvironmentPositiveMassConfig
  change (if hmem : site.val ∈
      finiteVolumeMassPairComplement site₁ site₂ then
        clippedMass (rest ⟨site.val, hmem⟩)
      else massLower) ∈ massSupport
  split_ifs
  · exact clippedMass_mem_support _
  · exact ⟨le_rfl, massLower_le_massUpper⟩

/-- Exact pair/complement reconstruction of the expected reduced child law
for an arbitrary iid mass ensemble. -/
theorem lintegral_childRepeatedReducedPerSitePairMeasure_eq_complement_conditional
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    (∫⁻ omega,
        childRepeatedReducedPerSitePairMeasure
          (ensemble.restrictPositiveMass (N := N) omega) A
        ∂ensemble.probability) =
      ∫⁻ rest,
        actualTwoMassChildRepeatedConditionalPerSiteMeasure
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂
          (actualTwoMassChildRepeatedPositivePairWeight
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂) A
        ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂)) := by
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  let _ : IsProbabilityMeasure
      (iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)) := by
    unfold iidFiniteMassVectorLaw
    infer_instance
  let observable : Lattice.PositiveMassConfig N → ENNReal := fun mass ↦
    childRepeatedReducedPerSitePairMeasure mass A
  have hmeasurable : Measurable fun state :
      (Real × Real) ×
        FiniteMassVector (finiteVolumeMassPairComplement site₁ site₂) ↦
      observable
        (finiteVolumePositiveMassPairReconstruction site₁ site₂ state) :=
    measurable_childRepeatedReducedPerSitePairMeasure_apply
      (finiteVolumePositiveMassPairReconstruction site₁ site₂)
      (measurable_finiteVolumePositiveMassPairReconstruction_mass
        site₁ site₂) hA
  rw [lintegral_finiteVolumePositiveMassConfig_eq_massPair_prod_complement
    ensemble site₁ site₂ hsite hmeasurable.aemeasurable]
  rw [lintegral_prod_symm' _ hmeasurable]
  apply lintegral_congr
  intro rest
  exact
    (actualTwoMassChildRepeatedConditionalPerSiteMeasure_apply_eq_lintegral_pairMeasure
      (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
      site₁ site₂ hA).symm

/-- The genuine canonical annealed reduced measure is exactly the integral
of actual two-mass conditional laws over the finite frozen environment. -/
theorem canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_eq_complement_conditional
    (n : Nat) (site₁ site₂ : Lattice.Site (n + 2))
    (hsite : site₁ ≠ site₂)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
      Measure (Real × Real)) A =
      ∫⁻ rest,
        actualTwoMassChildRepeatedConditionalPerSiteMeasure
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂
          (actualTwoMassChildRepeatedPositivePairWeight
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂) A
        ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂)) := by
  rw [canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply n hA]
  simp_rw [map_canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_forgetRank]
  calc
    _ = ∫⁻ omega,
        childRepeatedReducedPerSitePairMeasure
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := n + 2) omega) A
        ∂ RandomEnsemble.canonicalLaw := by
      apply lintegral_congr
      intro omega
      exact congrArg (fun measure : Measure (Real × Real) ↦ measure A)
        (map_perSiteChildRepeatedFrequencyMeasure_eq_pairMeasure
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := n + 2) omega))
    _ = _ :=
      lintegral_childRepeatedReducedPerSitePairMeasure_eq_complement_conditional
        canonicalIIDMassPhaseEnsemble site₁ site₂ hsite hA

/-- A pointwise conditional estimate for every frozen environment integrates
to the same annealed estimate. -/
theorem canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_le_of_conditional
    (n : Nat) (site₁ site₂ : Lattice.Site (n + 2))
    (hsite : site₁ ≠ site₂)
    {A : Set (Real × Real)} (hA : MeasurableSet A)
    (bound : ENNReal)
    (hbound : ∀ rest,
      actualTwoMassChildRepeatedConditionalPerSiteMeasure
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂
        (actualTwoMassChildRepeatedPositivePairWeight
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂) A ≤ bound) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
      Measure (Real × Real)) A ≤ bound := by
  rw [canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_eq_complement_conditional
    n site₁ site₂ hsite hA]
  calc
    (∫⁻ rest,
        actualTwoMassChildRepeatedConditionalPerSiteMeasure
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂
          (actualTwoMassChildRepeatedPositivePairWeight
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂) A
        ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂))) ≤
      ∫⁻ _rest,
        bound
        ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂)) := by
      apply lintegral_mono
      intro rest
      exact hbound rest
    _ = bound := by
      rw [lintegral_const]
      simp [iidFiniteMassVectorLaw]

end

end ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
