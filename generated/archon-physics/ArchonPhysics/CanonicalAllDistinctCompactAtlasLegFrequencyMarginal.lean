import ArchonPhysics.ActualThreeMassAllDistinctJointCompactAtlasCoarea
import ArchonPhysics.CanonicalAllDistinctLegFrequencyMarginalConsumer

/-!
# Automatic compact-atlas all-distinct leg marginals

This module composes the genuine compact regular atlas for the actual
three-mass law with the canonical all-distinct leg-frequency consumer.
At fixed finite volume, all chart and coarea hypotheses are discharged
automatically.  For a frozen sequence, the only remaining input is the
displayed uniform ceiling for the normalized actual atlas budget.

Both endpoints are uniform in the choice of decay leg.  The bad contribution
is kept as the exact kernel-weighted bad mass; compact regular exhaustion by
itself supplies neither a mismatch gap nor decay of that term.
-/

namespace ArchonPhysics.CanonicalAllDistinctCompactAtlasLegFrequencyMarginal

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeTrace
open ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
open ArchonPhysics.ActualThreeMassAllDistinctJointCompactAtlasCoarea
open ArchonPhysics.ActualThreeMassAllDistinctLegMismatchDomination
open ArchonPhysics.ActualThreeMassLiftedCompactAtlasPerSiteScaling
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.CanonicalAllDistinctLegFrequencyMarginalConsumer
open ArchonPhysics.CanonicalAllDistinctRawLiftedLawIdentification
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FrequencyMismatchKernelMarginalDomination
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- At every fixed finite volume, a modewise compact subset of the genuine
regular source automatically supplies all coarea data needed for every
broadened decay-leg marginal.  No `hcoarea` argument remains. -/
theorem exists_actualThreeMassAllDistinctJointCompactAtlas_broadenedLeg_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (K : OrderedModeTriple N → Set MassTriple)
    (hKcompact : ∀ modes, IsCompact (K modes))
    (hKregular : ∀ modes, K modes ⊆
      actualThreeMassProjectorRegularSource
        fixed site₀ site₁ site₂ modes) :
    ∃ detLower : OrderedModeTriple N → Real,
      ∃ atlasCard : OrderedModeTriple N → Nat,
        (∀ modes, 0 < detLower modes) ∧
        ∀ {T : Real}, 0 < T → ∀ leg : Fin 3,
          ∀ {target : Set Real}, MeasurableSet target →
            Measure.map (decayLiftedLegFrequency leg)
                ((actualThreeMassAllDistinctJointLiftedMeasure
                  fixed site₀ site₁ site₂ decayInteractionSign).withDensity
                    (liftedResonanceKernelDensity T)) target ≤
              (actualThreeMassAtlasRegularPerSiteBudget atlasCard
                    (fun _ => ENNReal.ofReal
                      (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
                    detLower * ENNReal.ofReal (Real.sqrt 5)) *
                  (volume : Measure Real) target +
                actualThreeMassWeightedBadPerSiteBudget
                  fixed site₀ site₁ site₂ decayInteractionSign
                  (actualThreeMassAllDistinctTupleWeight
                    fixed site₀ site₁ site₂) K T := by
  obtain ⟨detLower, atlasCard, hdetLower, hcoarea⟩ :=
    exists_actualThreeMassAllDistinctJointCompactAtlasCoareaBound
      fixed hfixed h₁₀ h₂₀ h₂₁ decayInteractionSign
        K hKcompact hKregular
  refine ⟨detLower, atlasCard, hdetLower, ?_⟩
  intro T hT leg target htarget
  exact
    actualThreeMassAllDistinctJoint_broadenedLeg_apply_le_of_jointCoarea
      fixed hfixed site₀ site₁ site₂ K
      (fun modes => (hKcompact modes).isClosed.measurableSet)
      (actualThreeMassAtlasRegularPerSiteBudget atlasCard
        (fun _ => ENNReal.ofReal
          (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8)) detLower)
      hcoarea hT leg htarget

/-- Frozen-sequence, all-three-leg endpoint.  Actual compact atlases and
positive determinant lower bounds are selected at every volume.  A single
ceiling `C` for their normalized costs then controls every volume, every
positive broadening time, and every decay leg. -/
theorem
  exists_actualThreeMassAllDistinctFrozenSequence_broadenedLeg_apply_le_of_uniformCompactAtlasBudget
    (fixed : (n : Nat) → Lattice.PositiveMassConfig (n + 3))
    (hfixed : ∀ n site, (fixed n).mass site ∈ massSupport)
    (site₀ site₁ site₂ : (n : Nat) → Lattice.Site (n + 3))
    (h₁₀ : ∀ n, site₁ n ≠ site₀ n)
    (h₂₀ : ∀ n, site₂ n ≠ site₀ n)
    (h₂₁ : ∀ n, site₂ n ≠ site₁ n)
    (K : (n : Nat) → OrderedModeTriple (n + 3) → Set MassTriple)
    (hKcompact : ∀ n modes, IsCompact (K n modes))
    (hKregular : ∀ n modes, K n modes ⊆
      actualThreeMassProjectorRegularSource
        (fixed n) (site₀ n) (site₁ n) (site₂ n) modes) :
    ∃ detLower : (n : Nat) → OrderedModeTriple (n + 3) → Real,
      ∃ atlasCard : (n : Nat) → OrderedModeTriple (n + 3) → Nat,
        (∀ n modes, 0 < detLower n modes) ∧
        ∀ {C : ENNReal},
          (∀ n,
            actualThreeMassAtlasRegularPerSiteBudget (atlasCard n)
                (fun _ => ENNReal.ofReal
                  (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
                (detLower n) ≤ C) →
            ∀ n {T : Real}, 0 < T → ∀ leg : Fin 3,
              ∀ {target : Set Real}, MeasurableSet target →
                Measure.map (decayLiftedLegFrequency leg)
                    ((actualThreeMassAllDistinctJointLiftedMeasure
                      (fixed n) (site₀ n) (site₁ n) (site₂ n)
                        decayInteractionSign).withDensity
                      (liftedResonanceKernelDensity T)) target ≤
                  (C * ENNReal.ofReal (Real.sqrt 5)) *
                      (volume : Measure Real) target +
                    actualThreeMassWeightedBadPerSiteBudget
                      (fixed n) (site₀ n) (site₁ n) (site₂ n)
                      decayInteractionSign
                      (actualThreeMassAllDistinctTupleWeight
                        (fixed n) (site₀ n) (site₁ n) (site₂ n))
                      (K n) T := by
  obtain ⟨detLower, atlasCard, hdetLower, hcoarea⟩ :=
    exists_actualThreeMassAllDistinctFrozenSequenceJointCoareaBound_of_uniformCompactAtlasBudget
      fixed hfixed site₀ site₁ site₂ h₁₀ h₂₀ h₂₁
        decayInteractionSign K hKcompact hKregular
  refine ⟨detLower, atlasCard, hdetLower, ?_⟩
  intro C hbudget n T hT leg target htarget
  exact
    actualThreeMassAllDistinctJoint_broadenedLeg_apply_le_of_jointCoarea
      (fixed n) (hfixed n) (site₀ n) (site₁ n) (site₂ n) (K n)
      (fun modes => (hKcompact n modes).isClosed.measurableSet)
      C (hcoarea hbudget n) hT leg htarget


/-! ## Exact annealed raw-law transport -/

variable {X Alpha Beta : Type*} [MeasurableSpace X]
  [MeasurableSpace Alpha] [MeasurableSpace Beta]

/-- A measurable weighted Dirac kernel packages fixed-density broadening and
a measurable projection as a Giry bind. -/
def weightedDiracKernel (f : Alpha → Beta) (g : Alpha → ENNReal)
    (x : Alpha) : Measure Beta := g x • Measure.dirac (f x)

theorem measurable_weightedDiracKernel
    {f : Alpha → Beta} (hf : Measurable f)
    {g : Alpha → ENNReal} (hg : Measurable g) :
    Measurable (weightedDiracKernel f g) := by
  refine Measure.measurable_of_measurable_coe _ fun target htarget => ?_
  simp only [weightedDiracKernel, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ htarget]
  exact hg.mul (measurable_one.indicator (hf htarget))

/-- Binding the weighted Dirac kernel is exactly density weighting followed
by pushforward. -/
theorem bind_weightedDiracKernel_eq_map_withDensity
    (mu : Measure Alpha) {f : Alpha → Beta} (hf : Measurable f)
    {g : Alpha → ENNReal} (hg : Measurable g) :
    mu.bind (weightedDiracKernel f g) =
      Measure.map f (mu.withDensity g) := by
  ext target htarget
  rw [Measure.bind_apply htarget
      (measurable_weightedDiracKernel hf hg).aemeasurable,
    Measure.map_apply hf htarget,
    withDensity_apply _ (hf htarget)]
  simp only [weightedDiracKernel, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ htarget]
  rw [← MeasureTheory.lintegral_indicator (hf htarget)]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ target
  · simp [hx]
  · simp [hx]

/-- A Giry-measurable family remains measurable after applying one fixed
measurable density and one fixed measurable pushforward. -/
theorem measurable_map_withDensity_of_measurable_measure
    (mu : X → Measure Alpha) (hmu : Measurable mu)
    {f : Alpha → Beta} (hf : Measurable f)
    {g : Alpha → ENNReal} (hg : Measurable g) :
    Measurable fun x => Measure.map f ((mu x).withDensity g) := by
  rw [show (fun x => Measure.map f ((mu x).withDensity g)) =
      fun x => (mu x).bind (weightedDiracKernel f g) by
    funext x
    exact (bind_weightedDiracKernel_eq_map_withDensity
      (mu x) hf hg).symm]
  exact (Measure.measurable_bind'
    (measurable_weightedDiracKernel hf hg)).comp hmu

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The canonical raw all-distinct lifted measure is Giry-measurable for
every coordinatewise measurable positive-mass sample. -/
theorem measurable_allDistinctPerSiteRawLiftedMeasure
    {Y : Type*} [MeasurableSpace Y] {N : Nat} [NeZero N]
    (massSample : Y → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun y => (massSample y).mass site)
    (sign : Fin 3 → InteractionSign) :
    Measurable fun y =>
      allDistinctPerSiteRawLiftedMeasure (massSample y) sign := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  exact measurable_allDistinctPerSiteRawLiftedMeasure_apply
    massSample hmass sign hA

/-- The actual conditional lifted law is a Giry-measurable function of the
finite iid complementary environment. -/
theorem measurable_actualThreeMassAllDistinctJointLiftedMeasure_finiteEnvironment
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign) :
    Measurable fun rest : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) =>
      actualThreeMassAllDistinctJointLiftedMeasure
        (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
        site₀ site₁ site₂ sign := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hjoint : Measurable fun state : MassTriple × FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂) =>
      allDistinctPerSiteRawLiftedMeasure
        (finiteVolumePositiveMassReconstruction site₀ site₁ site₂ state)
        sign A :=
    measurable_allDistinctPerSiteRawLiftedMeasure_apply
      (finiteVolumePositiveMassReconstruction site₀ site₁ site₂)
      (fun site => measurable_finiteVolumePositiveMassReconstruction_mass
        site₀ site₁ site₂ site) sign hA
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  let _ : IsProbabilityMeasure iidMassTripleLaw := by
    unfold iidMassTripleLaw
    infer_instance
  have hswap : Measurable fun state : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂) × MassTriple =>
      allDistinctPerSiteRawLiftedMeasure
        (finiteVolumePositiveMassReconstruction
          site₀ site₁ site₂ (state.2, state.1)) sign A := by
    change Measurable ((fun state : MassTriple × FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) =>
        allDistinctPerSiteRawLiftedMeasure
          (finiteVolumePositiveMassReconstruction
            site₀ site₁ site₂ state) sign A) ∘
      fun state : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) × MassTriple =>
          (state.2, state.1))
    exact hjoint.comp (measurable_snd.prodMk measurable_fst)
  have hparam : Measurable fun rest : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂) =>
      ∫⁻ triple,
        allDistinctPerSiteRawLiftedMeasure
          (finiteVolumePositiveMassReconstruction
            site₀ site₁ site₂ (triple, rest)) sign A
        ∂iidMassTripleLaw :=
    hswap.lintegral_prod_right
  convert hparam using 1
  funext rest
  simpa [finiteVolumePositiveMassReconstruction] using
    (actualThreeMassAllDistinctJointLiftedMeasure_apply_eq_lintegral_raw
      (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
      site₀ site₁ site₂ sign hA)

/-- The existing setwise raw-law Fubini identification upgrades to equality
of the two annealed lifted measures. -/
theorem bind_allDistinctPerSiteRawLiftedMeasure_eq_complement
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    (sign : Fin 3 → InteractionSign) :
    ensemble.probability.bind (fun omega =>
      allDistinctPerSiteRawLiftedMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign) =
      (iidFiniteMassVectorLaw
        (finiteVolumeMassComplement site₀ site₁ site₂)).bind (fun rest =>
          actualThreeMassAllDistinctJointLiftedMeasure
            (finiteEnvironmentPositiveMassConfig
              site₀ site₁ site₂ rest)
            site₀ site₁ site₂ sign) := by
  have hraw : Measurable fun omega =>
      allDistinctPerSiteRawLiftedMeasure
        (ensemble.restrictPositiveMass (N := N) omega) sign :=
    measurable_allDistinctPerSiteRawLiftedMeasure
      (fun omega => ensemble.restrictPositiveMass (N := N) omega)
      (fun site => by
        simpa only [IIDMassPhaseEnsemble.restrictPositiveMass_mass] using
          ensemble.mass_measurable site.val) sign
  have hactual : Measurable fun rest :
      FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) =>
      actualThreeMassAllDistinctJointLiftedMeasure
        (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
        site₀ site₁ site₂ sign :=
    measurable_actualThreeMassAllDistinctJointLiftedMeasure_finiteEnvironment
      site₀ site₁ site₂ sign
  ext A hA
  rw [Measure.bind_apply hA hraw.aemeasurable,
    Measure.bind_apply hA hactual.aemeasurable]
  exact lintegral_allDistinctPerSiteRawLiftedMeasure_eq_complement
    ensemble site₀ site₁ site₂ h₀₁ h₀₂ h₁₂ sign hA


/-- Broadening by the normalized resonance kernel and projection to any
decay-leg frequency commute with the exact finite-volume iid Fubini
identification. -/
theorem lintegral_allDistinctPerSiteRawLiftedMeasure_broadenedLeg_eq_complement
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    {T : Real} (hT : 0 < T) (leg : Fin 3)
    {target : Set Real} (htarget : MeasurableSet target) :
    (∫⁻ omega,
      Measure.map (decayLiftedLegFrequency leg)
        ((allDistinctPerSiteRawLiftedMeasure
          (ensemble.restrictPositiveMass (N := N) omega)
          RandomMassThreeWaveCollisionNetwork.decayInteractionSign).withDensity
            (liftedResonanceKernelDensity T)) target
      ∂ensemble.probability) =
      ∫⁻ rest,
        Measure.map (decayLiftedLegFrequency leg)
          ((actualThreeMassAllDistinctJointLiftedMeasure
            (finiteEnvironmentPositiveMassConfig
              site₀ site₁ site₂ rest)
            site₀ site₁ site₂
            RandomMassThreeWaveCollisionNetwork.decayInteractionSign).withDensity
              (liftedResonanceKernelDensity T)) target
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂) := by
  let raw : Omega → Measure MassTriple := fun omega =>
    allDistinctPerSiteRawLiftedMeasure
      (ensemble.restrictPositiveMass (N := N) omega)
      RandomMassThreeWaveCollisionNetwork.decayInteractionSign
  let actual : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂) → Measure MassTriple :=
    fun rest => actualThreeMassAllDistinctJointLiftedMeasure
      (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
      site₀ site₁ site₂
      RandomMassThreeWaveCollisionNetwork.decayInteractionSign
  let kernel : MassTriple → Measure Real :=
    weightedDiracKernel (decayLiftedLegFrequency leg)
      (liftedResonanceKernelDensity T)
  have hraw : Measurable raw :=
    measurable_allDistinctPerSiteRawLiftedMeasure
      (fun omega => ensemble.restrictPositiveMass (N := N) omega)
      (fun site => by
        simpa only [IIDMassPhaseEnsemble.restrictPositiveMass_mass] using
          ensemble.mass_measurable site.val)
      RandomMassThreeWaveCollisionNetwork.decayInteractionSign
  have hactual : Measurable actual :=
    measurable_actualThreeMassAllDistinctJointLiftedMeasure_finiteEnvironment
      site₀ site₁ site₂
      RandomMassThreeWaveCollisionNetwork.decayInteractionSign
  have hfrequency : Measurable (decayLiftedLegFrequency leg) :=
    measurable_decayLiftedLegFrequency leg
  have hkernelDensity : Measurable (liftedResonanceKernelDensity T) :=
    measurable_liftedResonanceKernelDensity hT
  have hkernel : Measurable kernel :=
    measurable_weightedDiracKernel hfrequency hkernelDensity
  have hrawProcessed : Measurable fun omega =>
      Measure.map (decayLiftedLegFrequency leg)
        ((raw omega).withDensity (liftedResonanceKernelDensity T)) :=
    measurable_map_withDensity_of_measurable_measure raw hraw
      hfrequency hkernelDensity
  have hactualProcessed : Measurable fun rest =>
      Measure.map (decayLiftedLegFrequency leg)
        ((actual rest).withDensity (liftedResonanceKernelDensity T)) :=
    measurable_map_withDensity_of_measurable_measure actual hactual
      hfrequency hkernelDensity
  have hrawProcessedEq :
      (fun omega => Measure.map (decayLiftedLegFrequency leg)
        ((raw omega).withDensity (liftedResonanceKernelDensity T))) =
      (fun omega => (raw omega).bind kernel) := by
    funext omega
    exact (bind_weightedDiracKernel_eq_map_withDensity
      (raw omega) hfrequency hkernelDensity).symm
  have hactualProcessedEq :
      (fun rest => Measure.map (decayLiftedLegFrequency leg)
        ((actual rest).withDensity (liftedResonanceKernelDensity T))) =
      (fun rest => (actual rest).bind kernel) := by
    funext rest
    exact (bind_weightedDiracKernel_eq_map_withDensity
      (actual rest) hfrequency hkernelDensity).symm
  have hrawBind : ensemble.probability.bind raw =
      (iidFiniteMassVectorLaw
        (finiteVolumeMassComplement site₀ site₁ site₂)).bind actual :=
    bind_allDistinctPerSiteRawLiftedMeasure_eq_complement
      ensemble site₀ site₁ site₂ h₀₁ h₀₂ h₁₂
      RandomMassThreeWaveCollisionNetwork.decayInteractionSign
  change (∫⁻ omega,
      Measure.map (decayLiftedLegFrequency leg)
        ((raw omega).withDensity (liftedResonanceKernelDensity T)) target
      ∂ensemble.probability) =
    ∫⁻ rest,
      Measure.map (decayLiftedLegFrequency leg)
        ((actual rest).withDensity (liftedResonanceKernelDensity T)) target
      ∂iidFiniteMassVectorLaw
        (finiteVolumeMassComplement site₀ site₁ site₂)
  calc
    _ = ensemble.probability.bind (fun omega =>
          Measure.map (decayLiftedLegFrequency leg)
            ((raw omega).withDensity
              (liftedResonanceKernelDensity T))) target :=
      (Measure.bind_apply htarget hrawProcessed.aemeasurable).symm
    _ = ensemble.probability.bind (fun omega =>
          (raw omega).bind kernel) target := by
      rw [hrawProcessedEq]
    _ = (ensemble.probability.bind raw).bind kernel target :=
      congrArg (fun measure : Measure Real => measure target)
        (Measure.bind_bind hraw.aemeasurable hkernel.aemeasurable).symm
    _ = ((iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂)).bind
            actual).bind kernel target := by rw [hrawBind]
    _ = (iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂)).bind
          (fun rest => (actual rest).bind kernel) target :=
      congrArg (fun measure : Measure Real => measure target)
        (Measure.bind_bind hactual.aemeasurable hkernel.aemeasurable)
    _ = (iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂)).bind
          (fun rest => Measure.map (decayLiftedLegFrequency leg)
            ((actual rest).withDensity
              (liftedResonanceKernelDensity T))) target := by
      rw [hactualProcessedEq]
    _ = ∫⁻ rest,
          Measure.map (decayLiftedLegFrequency leg)
            ((actual rest).withDensity
              (liftedResonanceKernelDensity T)) target
          ∂iidFiniteMassVectorLaw
            (finiteVolumeMassComplement site₀ site₁ site₂) :=
      Measure.bind_apply htarget hactualProcessed.aemeasurable

/-- Complete finite-volume canonical annealed all-distinct leg marginal.
For every measurable target and every positive broadening time, actual
compact regular atlases are selected in every complementary environment.
No fixed-volume coarea premise remains; the right side records only the
constructed atlas cost and the exact weighted bad contribution. -/
theorem exists_actualThreeMassAllDistinctCompactAtlas_annealed_broadenedLeg_apply_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    (K : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) →
      OrderedModeTriple N → Set MassTriple)
    (hKcompact : ∀ rest modes, IsCompact (K rest modes))
    (hKregular : ∀ rest modes, K rest modes ⊆
      actualThreeMassProjectorRegularSource
        (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
        site₀ site₁ site₂ modes)
    {T : Real} (hT : 0 < T) (leg : Fin 3)
    {target : Set Real} (htarget : MeasurableSet target) :
    ∃ detLower : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) →
      OrderedModeTriple N → Real,
      ∃ atlasCard : FiniteMassVector
          (finiteVolumeMassComplement site₀ site₁ site₂) →
        OrderedModeTriple N → Nat,
        (∀ rest modes, 0 < detLower rest modes) ∧
        (∫⁻ omega,
          Measure.map (decayLiftedLegFrequency leg)
            ((allDistinctPerSiteRawLiftedMeasure
              (ensemble.restrictPositiveMass (N := N) omega)
              RandomMassThreeWaveCollisionNetwork.decayInteractionSign).withDensity
                (liftedResonanceKernelDensity T)) target
          ∂ensemble.probability) ≤
          ∫⁻ rest,
            ((actualThreeMassAtlasRegularPerSiteBudget (atlasCard rest)
                  (fun _ => ENNReal.ofReal
                    (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
                  (detLower rest) *
                ENNReal.ofReal (Real.sqrt 5)) *
              (volume : Measure Real) target +
            actualThreeMassWeightedBadPerSiteBudget
              (finiteEnvironmentPositiveMassConfig
                site₀ site₁ site₂ rest)
              site₀ site₁ site₂
              RandomMassThreeWaveCollisionNetwork.decayInteractionSign
              (actualThreeMassAllDistinctTupleWeight
                (finiteEnvironmentPositiveMassConfig
                  site₀ site₁ site₂ rest)
                site₀ site₁ site₂)
              (K rest) T)
          ∂iidFiniteMassVectorLaw
            (finiteVolumeMassComplement site₀ site₁ site₂) := by
  have hrest (rest : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂)) :=
    exists_actualThreeMassAllDistinctJointCompactAtlas_broadenedLeg_apply_le
      (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
      (finiteEnvironmentPositiveMassConfig_mass_mem_support
        site₀ site₁ site₂ rest)
      h₀₁.symm h₀₂.symm h₁₂.symm
      (K rest) (hKcompact rest) (hKregular rest)
  choose detLower atlasCard hdetLower hbound using hrest
  refine ⟨detLower, atlasCard, hdetLower, ?_⟩
  rw [lintegral_allDistinctPerSiteRawLiftedMeasure_broadenedLeg_eq_complement
    ensemble site₀ site₁ site₂ h₀₁ h₀₂ h₁₂ hT leg htarget]
  exact lintegral_mono fun rest => hbound rest hT leg htarget


/-- If the automatically selected finite-volume atlas costs have one ceiling
over all complementary environments, the complete canonical annealed bound
uses that same constant for every positive time and every decay leg. -/
theorem
  exists_actualThreeMassAllDistinctCompactAtlas_annealed_broadenedLeg_apply_le_of_uniformBudget
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    (K : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) →
      OrderedModeTriple N → Set MassTriple)
    (hKcompact : ∀ rest modes, IsCompact (K rest modes))
    (hKregular : ∀ rest modes, K rest modes ⊆
      actualThreeMassProjectorRegularSource
        (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
        site₀ site₁ site₂ modes) :
    ∃ detLower : FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) →
      OrderedModeTriple N → Real,
      ∃ atlasCard : FiniteMassVector
          (finiteVolumeMassComplement site₀ site₁ site₂) →
        OrderedModeTriple N → Nat,
        (∀ rest modes, 0 < detLower rest modes) ∧
        ∀ {C : ENNReal},
          (∀ rest,
            actualThreeMassAtlasRegularPerSiteBudget (atlasCard rest)
                (fun _ => ENNReal.ofReal
                  (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
                (detLower rest) ≤ C) →
            ∀ {T : Real}, 0 < T → ∀ leg : Fin 3,
              ∀ {target : Set Real}, MeasurableSet target →
                (∫⁻ omega,
                  Measure.map (decayLiftedLegFrequency leg)
                    ((allDistinctPerSiteRawLiftedMeasure
                      (ensemble.restrictPositiveMass (N := N) omega)
                      RandomMassThreeWaveCollisionNetwork.decayInteractionSign).withDensity
                        (liftedResonanceKernelDensity T)) target
                  ∂ensemble.probability) ≤
                  ∫⁻ rest,
                    (C * ENNReal.ofReal (Real.sqrt 5)) *
                        (volume : Measure Real) target +
                      actualThreeMassWeightedBadPerSiteBudget
                        (finiteEnvironmentPositiveMassConfig
                          site₀ site₁ site₂ rest)
                        site₀ site₁ site₂
                        RandomMassThreeWaveCollisionNetwork.decayInteractionSign
                        (actualThreeMassAllDistinctTupleWeight
                          (finiteEnvironmentPositiveMassConfig
                            site₀ site₁ site₂ rest)
                          site₀ site₁ site₂)
                        (K rest) T
                    ∂iidFiniteMassVectorLaw
                      (finiteVolumeMassComplement site₀ site₁ site₂) := by
  have hrest (rest : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂)) :=
    exists_actualThreeMassAllDistinctJointCompactAtlas_broadenedLeg_apply_le
      (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ rest)
      (finiteEnvironmentPositiveMassConfig_mass_mem_support
        site₀ site₁ site₂ rest)
      h₀₁.symm h₀₂.symm h₁₂.symm
      (K rest) (hKcompact rest) (hKregular rest)
  choose detLower atlasCard hdetLower hbound using hrest
  refine ⟨detLower, atlasCard, hdetLower, ?_⟩
  intro C hbudget T hT leg target htarget
  rw [lintegral_allDistinctPerSiteRawLiftedMeasure_broadenedLeg_eq_complement
    ensemble site₀ site₁ site₂ h₀₁ h₀₂ h₁₂ hT leg htarget]
  apply lintegral_mono
  intro rest
  calc
    _ ≤ ((actualThreeMassAtlasRegularPerSiteBudget (atlasCard rest)
              (fun _ => ENNReal.ofReal
                (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
              (detLower rest) * ENNReal.ofReal (Real.sqrt 5)) *
            (volume : Measure Real) target +
          actualThreeMassWeightedBadPerSiteBudget
            (finiteEnvironmentPositiveMassConfig
              site₀ site₁ site₂ rest)
            site₀ site₁ site₂ decayInteractionSign
            (actualThreeMassAllDistinctTupleWeight
              (finiteEnvironmentPositiveMassConfig
                site₀ site₁ site₂ rest)
              site₀ site₁ site₂)
            (K rest) T) := hbound rest hT leg htarget
    _ ≤ (C * ENNReal.ofReal (Real.sqrt 5)) *
            (volume : Measure Real) target +
          actualThreeMassWeightedBadPerSiteBudget
            (finiteEnvironmentPositiveMassConfig
              site₀ site₁ site₂ rest)
            site₀ site₁ site₂ decayInteractionSign
            (actualThreeMassAllDistinctTupleWeight
              (finiteEnvironmentPositiveMassConfig
                site₀ site₁ site₂ rest)
              site₀ site₁ site₂)
            (K rest) T := by
      gcongr
      exact hbudget rest

end

end ArchonPhysics.CanonicalAllDistinctCompactAtlasLegFrequencyMarginal
