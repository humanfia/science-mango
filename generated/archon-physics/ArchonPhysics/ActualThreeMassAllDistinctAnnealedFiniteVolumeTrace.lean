import ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningBridge

/-!
# Finite-volume iid complement formula for the all-distinct trace

Three distinct physical mass sites are split from the finite iid block.  The
ensemble expectation of the genuine all-distinct squared-sinc trace is then
exactly the complement average of the actual conditional three-mass lifted
law.  This is the model-facing annealed trace identity.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeTrace

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningBridge
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Every reconstructed physical mass coordinate is measurable in the
selected triple and the finite complementary vector. -/
theorem measurable_finiteVolumePositiveMassReconstruction_mass
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ site : Lattice.Site N) :
    Measurable fun state : MassTriple × FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) =>
      (finiteVolumePositiveMassReconstruction
        site₀ site₁ site₂ state).mass site := by
  unfold finiteVolumePositiveMassReconstruction threeMassSiteConfig
  by_cases hsite₀ : site = site₀
  · subst site
    simp only [ite_true]
    unfold clippedMass
    fun_prop
  · simp only [hsite₀, ite_false]
    by_cases hsite₁ : site = site₁
    · subst site
      simp only [ite_true]
      unfold clippedMass
      fun_prop
    · simp only [hsite₁, ite_false]
      by_cases hsite₂ : site = site₂
      · subst site
        simp only [ite_true]
        unfold clippedMass
        fun_prop
      · simp only [hsite₂, ite_false]
        change Measurable fun state :
            MassTriple × FiniteMassVector
              (finiteVolumeMassComplement site₀ site₁ site₂) =>
          if hmem : site.val ∈
              finiteVolumeMassComplement site₀ site₁ site₂ then
            clippedMass (state.2 ⟨site.val, hmem⟩)
          else massLower
        split_ifs with hmem
        · unfold clippedMass
          fun_prop
        · exact measurable_const

/-- The frozen complementary environment remains in the frozen iid mass
support, including its harmless selected-site placeholders. -/
theorem finiteEnvironmentPositiveMassConfig_mass_mem_support
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (rest : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂)) :
    ∀ site,
      (finiteEnvironmentPositiveMassConfig
        site₀ site₁ site₂ rest).mass site ∈ massSupport := by
  intro site
  change (if hmem : site.val ∈
      finiteVolumeMassComplement site₀ site₁ site₂ then
    clippedMass (rest ⟨site.val, hmem⟩)
  else massLower) ∈ massSupport
  split_ifs
  · exact clippedMass_mem_support _
  · simp only [massSupport, Set.mem_Icc]
    norm_num [massLower, massUpper]

/-- Exact annealed finite-volume reconstruction: the expected all-distinct
broadening trace equals the complement average of the actual conditional
three-mass trace. -/
theorem lintegral_allDistinctPerSiteBroadenedTrace_eq_complement
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    (sign : Fin 3 → InteractionSign) {T : Real} (hT : 0 < T) :
    (∫⁻ omega,
      allDistinctPerSiteBroadenedTrace
        (ensemble.restrictPositiveMass (N := N) omega) sign T
      ∂ensemble.probability) =
      ∫⁻ rest,
        actualThreeMassAllDistinctConditionalBroadenedChildMeasure
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ sign T Set.univ
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂) := by
  let observable : Lattice.PositiveMassConfig N → ENNReal := fun mass =>
    allDistinctPerSiteBroadenedTrace mass sign T
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  let _ : IsProbabilityMeasure iidMassTripleLaw := by
    unfold iidMassTripleLaw
    infer_instance
  let _ : IsProbabilityMeasure (iidFiniteMassVectorLaw
      (finiteVolumeMassComplement site₀ site₁ site₂)) := by
    unfold iidFiniteMassVectorLaw
    infer_instance
  have hobservable : Measurable fun state :
      MassTriple × FiniteMassVector
        (finiteVolumeMassComplement site₀ site₁ site₂) =>
      observable (finiteVolumePositiveMassReconstruction
        site₀ site₁ site₂ state) :=
    measurable_allDistinctPerSiteBroadenedTrace
      (finiteVolumePositiveMassReconstruction site₀ site₁ site₂)
      (fun site =>
        measurable_finiteVolumePositiveMassReconstruction_mass
          site₀ site₁ site₂ site) sign hT
  calc
    (∫⁻ omega,
        observable (ensemble.restrictPositiveMass (N := N) omega)
        ∂ensemble.probability) =
      ∫⁻ state,
        observable (finiteVolumePositiveMassReconstruction
          site₀ site₁ site₂ state)
        ∂(iidMassTripleLaw.prod
          (iidFiniteMassVectorLaw
            (finiteVolumeMassComplement site₀ site₁ site₂))) :=
      lintegral_finiteVolumePositiveMassConfig_eq_massTriple_prod_complement
        ensemble site₀ site₁ site₂ h₀₁ h₀₂ h₁₂
          hobservable.aemeasurable
    _ = ∫⁻ rest,
        ∫⁻ triple,
          observable (finiteVolumePositiveMassReconstruction
            site₀ site₁ site₂ (triple, rest))
          ∂iidMassTripleLaw
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂) :=
      lintegral_prod_symm _ hobservable.aemeasurable
    _ = ∫⁻ rest,
        actualThreeMassAllDistinctConditionalBroadenedChildMeasure
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ sign T Set.univ
        ∂iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂) := by
      apply lintegral_congr
      intro rest
      simpa [observable, finiteVolumePositiveMassReconstruction] using
        lintegral_allDistinctPerSiteBroadenedTrace_threeMassSiteConfig_eq
          (finiteEnvironmentPositiveMassConfig
            site₀ site₁ site₂ rest)
          site₀ site₁ site₂ sign hT

end


end ArchonPhysics.ActualThreeMassAllDistinctAnnealedFiniteVolumeTrace
