import ArchonPhysics.IIDMassTripleFiniteEnvironment
import ArchonPhysics.ActualTwoMassSpectralChart

/-!
# Exact finite-volume reconstruction from two masses and their complement

Two distinct mass coordinates are split from a finite iid block.  The pair
and the complementary finite vector have the exact product law
`iidMassPairLaw × iidFiniteMassVectorLaw`, and reinsertion through the actual
two-mass spectral family reconstructs the original positive mass
configuration pointwise.
-/

namespace ArchonPhysics.IIDMassPairFiniteVolumeReconstruction

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory ProbabilityTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Two selected physical mass coordinates. -/
def ensembleMassPair
    (ensemble : IIDMassPhaseEnsemble Omega)
    (i j : Nat) (omega : Omega) : Real × Real :=
  (ensemble.mass i omega, ensemble.mass j omega)

theorem measurable_ensembleMassPair
    (ensemble : IIDMassPhaseEnsemble Omega) (i j : Nat) :
    Measurable (ensembleMassPair ensemble i j) :=
  (ensemble.mass_measurable i).prodMk (ensemble.mass_measurable j)

/-- Two distinct iid coordinates have exactly the concrete pair law used by
the actual two-mass chart. -/
theorem ensembleMassPair_hasLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    {i j : Nat} (hij : i ≠ j) :
    HasLaw (ensembleMassPair ensemble i j)
      iidMassPairLaw ensemble.probability := by
  let _ : IsFiniteMeasure ensemble.probability :=
    ⟨by rw [ensemble.probability_univ]; norm_num⟩
  have hindep : IndepFun (ensemble.mass i) (ensemble.mass j)
      ensemble.probability :=
    ensemble.mass_iIndep.indepFun hij
  change HasLaw
    (fun omega => (ensemble.mass i omega, ensemble.mass j omega))
    (massCoordinateLaw.prod massCoordinateLaw) ensemble.probability
  exact hindep.hasLaw_prod (ensemble.mass_hasLaw i) (ensemble.mass_hasLaw j)

/-- The finite set containing the two selected coordinates. -/
def selectedMassPairIndices (i j : Nat) : Finset Nat :=
  {i, j}

/-- The selected pair is independent of every disjoint finite frozen mass
environment. -/
theorem ensembleMassPair_indep_finiteEnvironment
    (ensemble : IIDMassPhaseEnsemble Omega)
    (i j : Nat) (rest : Finset Nat)
    (hi : i ∉ rest) (hj : j ∉ rest) :
    IndepFun
      (ensembleMassPair ensemble i j)
      (ensembleFiniteMassVector ensemble rest)
      ensemble.probability := by
  have hdisjoint : Disjoint (selectedMassPairIndices i j) rest := by
    rw [Finset.disjoint_left]
    intro index hselected hrest
    simp only [selectedMassPairIndices, Finset.mem_insert,
      Finset.mem_singleton] at hselected
    rcases hselected with hindex | hindex
    · exact hi (hindex ▸ hrest)
    · exact hj (hindex ▸ hrest)
  have hgroups :=
    ensemble.mass_iIndep.indepFun_finset
      (selectedMassPairIndices i j) rest hdisjoint ensemble.mass_measurable
  have hextract : Measurable
      (fun values : (index : selectedMassPairIndices i j) → Real =>
        (values ⟨i, by simp [selectedMassPairIndices]⟩,
          values ⟨j, by simp [selectedMassPairIndices]⟩)) :=
    (measurable_pi_apply
      (⟨i, by simp [selectedMassPairIndices]⟩ :
        selectedMassPairIndices i j)).prodMk
      (measurable_pi_apply
        (⟨j, by simp [selectedMassPairIndices]⟩ :
          selectedMassPairIndices i j))
  have hcomposed := hgroups.comp hextract measurable_id
  change IndepFun
    (fun omega => (ensemble.mass i omega, ensemble.mass j omega))
    (fun omega (index : rest) => ensemble.mass index.1 omega)
    ensemble.probability
  apply hcomposed.congr
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- Exact product law of the selected pair and its disjoint finite
environment. -/
theorem ensembleMassPair_prod_finiteEnvironment_hasLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    {i j : Nat} (hij : i ≠ j)
    (rest : Finset Nat) (hi : i ∉ rest) (hj : j ∉ rest) :
    HasLaw
      (fun omega =>
        (ensembleMassPair ensemble i j omega,
          ensembleFiniteMassVector ensemble rest omega))
      (iidMassPairLaw.prod (iidFiniteMassVectorLaw rest))
      ensemble.probability := by
  let _ : IsFiniteMeasure ensemble.probability :=
    ⟨by rw [ensemble.probability_univ]; norm_num⟩
  exact
    (ensembleMassPair_indep_finiteEnvironment
      ensemble i j rest hi hj).hasLaw_prod
        (ensembleMassPair_hasLaw ensemble hij)
        (ensembleFiniteMassVector_hasLaw ensemble rest)

/-- The finite-volume mass indices other than the two selected sites. -/
def finiteVolumeMassPairComplement
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) : Finset Nat :=
  Finset.range N \ selectedMassPairIndices site₁.val site₂.val

/-- Frozen positive environment obtained from the complementary vector.
Selected coordinates carry harmless placeholders because the chart replaces
them. -/
def finitePairEnvironmentPositiveMassConfig
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N)
    (rest : FiniteMassVector
      (finiteVolumeMassPairComplement site₁ site₂)) :
    Lattice.PositiveMassConfig N where
  mass site :=
    if hmem : site.val ∈ finiteVolumeMassPairComplement site₁ site₂ then
      clippedMass (rest ⟨site.val, hmem⟩)
    else massLower
  mass_pos site := by
    split_ifs
    · exact clippedMass_pos _
    · exact massLower_pos

/-- Reinsert the selected pair into its frozen environment through the
genuine actual two-mass configuration map. -/
def finiteVolumePositiveMassPairReconstruction
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N)
    (state : (Real × Real) × FiniteMassVector
      (finiteVolumeMassPairComplement site₁ site₂)) :
    Lattice.PositiveMassConfig N :=
  twoSiteMassConfig
    (finitePairEnvironmentPositiveMassConfig site₁ site₂ state.2)
    site₁ site₂ state.1

/-- The selected iid pair and complementary vector reconstruct the exact
finite-volume positive mass configuration pointwise. -/
theorem finiteVolumePositiveMassPairReconstruction_ensemble_eq
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    (omega : Omega) :
    finiteVolumePositiveMassPairReconstruction site₁ site₂
        (ensembleMassPair ensemble site₁.val site₂.val omega,
          ensembleFiniteMassVector ensemble
            (finiteVolumeMassPairComplement site₁ site₂) omega) =
      ensemble.restrictPositiveMass (N := N) omega := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext site
  by_cases hsite₁ : site = site₁
  · subst site
    simp [finiteVolumePositiveMassPairReconstruction, twoSiteMassConfig,
      ensembleMassPair,
      clippedMass_eq_self (ensemble.mass_mem_support site₁.val omega)]
  · by_cases hsite₂ : site = site₂
    · subst site
      simp [finiteVolumePositiveMassPairReconstruction, twoSiteMassConfig,
        ensembleMassPair, hsite.symm,
        clippedMass_eq_self (ensemble.mass_mem_support site₂.val omega)]
    · have hval₁ : site.val ≠ site₁.val := by
        intro hval
        exact hsite₁ (ZMod.val_injective N hval)
      have hval₂ : site.val ≠ site₂.val := by
        intro hval
        exact hsite₂ (ZMod.val_injective N hval)
      have hmem : site.val ∈
          finiteVolumeMassPairComplement site₁ site₂ := by
        simp [finiteVolumeMassPairComplement, selectedMassPairIndices,
          site.val_lt, hval₁, hval₂]
      simp [finiteVolumePositiveMassPairReconstruction, twoSiteMassConfig,
        finitePairEnvironmentPositiveMassConfig,
        ensembleFiniteMassVector, hsite₁, hsite₂, hmem,
        clippedMass_eq_self (ensemble.mass_mem_support site.val omega)]

/-- Exact finite-volume Fubini/resampling identity for every nonnegative
measurable observable of the full positive mass configuration. -/
theorem lintegral_finiteVolumePositiveMassConfig_eq_massPair_prod_complement
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₁ site₂ : Lattice.Site N) (hsite : site₁ ≠ site₂)
    {observable : Lattice.PositiveMassConfig N → ENNReal}
    (hmeasurable : AEMeasurable
      (fun state : (Real × Real) × FiniteMassVector
          (finiteVolumeMassPairComplement site₁ site₂) =>
        observable
          (finiteVolumePositiveMassPairReconstruction site₁ site₂ state))
      (iidMassPairLaw.prod
        (iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂)))) :
    ∫⁻ omega,
        observable (ensemble.restrictPositiveMass (N := N) omega)
        ∂ensemble.probability =
      ∫⁻ state,
        observable
          (finiteVolumePositiveMassPairReconstruction site₁ site₂ state)
        ∂(iidMassPairLaw.prod
          (iidFiniteMassVectorLaw
            (finiteVolumeMassPairComplement site₁ site₂))) := by
  have hval : site₁.val ≠ site₂.val := by
    intro heq
    exact hsite (ZMod.val_injective N heq)
  let rest := finiteVolumeMassPairComplement site₁ site₂
  have hsite₁Rest : site₁.val ∉ rest := by
    simp [rest, finiteVolumeMassPairComplement, selectedMassPairIndices]
  have hsite₂Rest : site₂.val ∉ rest := by
    simp [rest, finiteVolumeMassPairComplement, selectedMassPairIndices]
  have hresampling :=
    (ensembleMassPair_prod_finiteEnvironment_hasLaw
      ensemble hval rest hsite₁Rest hsite₂Rest).lintegral_comp hmeasurable
  calc
    ∫⁻ omega,
        observable (ensemble.restrictPositiveMass (N := N) omega)
        ∂ensemble.probability =
      ∫⁻ omega,
        observable
          (finiteVolumePositiveMassPairReconstruction site₁ site₂
            (ensembleMassPair ensemble site₁.val site₂.val omega,
              ensembleFiniteMassVector ensemble rest omega))
        ∂ensemble.probability := by
      apply lintegral_congr
      intro omega
      exact congrArg observable
        (finiteVolumePositiveMassPairReconstruction_ensemble_eq
          ensemble site₁ site₂ hsite omega).symm
    _ = ∫⁻ state,
        observable
          (finiteVolumePositiveMassPairReconstruction site₁ site₂ state)
        ∂(iidMassPairLaw.prod (iidFiniteMassVectorLaw rest)) :=
      hresampling

end

end ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
