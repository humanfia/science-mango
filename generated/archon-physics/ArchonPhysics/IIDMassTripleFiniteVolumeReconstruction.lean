import ArchonPhysics.IIDMassTripleFiniteEnvironment
import ArchonPhysics.ActualThreeMassLiftedSpectralChart

/-!
# Exact finite-volume reconstruction from three masses and their complement

At any finite periodic volume, remove three distinct mass coordinates from
the finite iid block.  A selected mass triple together with the complementary
finite vector reconstructs the full positive mass configuration exactly.
Combining this identity with the finite-environment product law yields the
precise Fubini formula for every nonnegative measurable finite-volume
spectral observable.
-/

namespace ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.IIDMassTripleMarginal
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The finite-volume mass indices other than the three selected sites. -/
def finiteVolumeMassComplement
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) : Finset Nat :=
  Finset.range N \ selectedMassIndices site₀.val site₁.val site₂.val

/-- A positive frozen environment obtained from the complementary vector.
Values at the selected sites are arbitrary placeholders, since the actual
three-mass chart replaces them. -/
def finiteEnvironmentPositiveMassConfig
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (rest : FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂)) :
    Lattice.PositiveMassConfig N where
  mass site :=
    if hmem : site.val ∈ finiteVolumeMassComplement site₀ site₁ site₂ then
      clippedMass (rest ⟨site.val, hmem⟩)
    else massLower
  mass_pos site := by
    split_ifs
    · exact clippedMass_pos _
    · exact massLower_pos

/-- Reinsert the selected triple into its frozen environment by the genuine
actual three-mass configuration map. -/
def finiteVolumePositiveMassReconstruction
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (state : MassTriple × FiniteMassVector
      (finiteVolumeMassComplement site₀ site₁ site₂)) :
    Lattice.PositiveMassConfig N :=
  threeMassSiteConfig
    (finiteEnvironmentPositiveMassConfig site₀ site₁ site₂ state.2)
    site₀ site₁ site₂ state.1

/-- The selected iid triple and complementary vector reconstruct the exact
finite-volume positive mass configuration pointwise. -/
theorem finiteVolumePositiveMassReconstruction_ensemble_eq
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (omega : Omega) :
    finiteVolumePositiveMassReconstruction site₀ site₁ site₂
        (ensembleMassTriple ensemble site₀.val site₁.val site₂.val omega,
          ensembleFiniteMassVector ensemble
            (finiteVolumeMassComplement site₀ site₁ site₂) omega) =
      ensemble.restrictPositiveMass (N := N) omega := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext site
  by_cases hsite₀ : site = site₀
  · subst site
    simp [finiteVolumePositiveMassReconstruction, threeMassSiteConfig,
      ensembleMassTriple,
      clippedMass_eq_self (ensemble.mass_mem_support site₀.val omega)]
  · by_cases hsite₁ : site = site₁
    · subst site
      simp [finiteVolumePositiveMassReconstruction, threeMassSiteConfig,
        ensembleMassTriple, hsite₀,
        clippedMass_eq_self (ensemble.mass_mem_support site₁.val omega)]
    · by_cases hsite₂ : site = site₂
      · subst site
        simp [finiteVolumePositiveMassReconstruction, threeMassSiteConfig,
          ensembleMassTriple, hsite₀, hsite₁,
          clippedMass_eq_self (ensemble.mass_mem_support site₂.val omega)]
      · have hval₀ : site.val ≠ site₀.val := by
          intro hval
          exact hsite₀ (ZMod.val_injective N hval)
        have hval₁ : site.val ≠ site₁.val := by
          intro hval
          exact hsite₁ (ZMod.val_injective N hval)
        have hval₂ : site.val ≠ site₂.val := by
          intro hval
          exact hsite₂ (ZMod.val_injective N hval)
        have hmem : site.val ∈
            finiteVolumeMassComplement site₀ site₁ site₂ := by
          simp [finiteVolumeMassComplement, selectedMassIndices,
            site.val_lt, hval₀, hval₁, hval₂]
        simp [finiteVolumePositiveMassReconstruction, threeMassSiteConfig,
          finiteEnvironmentPositiveMassConfig, ensembleFiniteMassVector,
          hsite₀, hsite₁, hsite₂, hmem,
          clippedMass_eq_self (ensemble.mass_mem_support site.val omega)]

/-- Exact finite-volume Fubini/resampling formula for any nonnegative
measurable observable of the full positive mass configuration. -/
theorem lintegral_finiteVolumePositiveMassConfig_eq_massTriple_prod_complement
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N)
    (h₀₁ : site₀ ≠ site₁) (h₀₂ : site₀ ≠ site₂)
    (h₁₂ : site₁ ≠ site₂)
    {observable : Lattice.PositiveMassConfig N → ENNReal}
    (hmeasurable : AEMeasurable
      (fun state : MassTriple × FiniteMassVector
          (finiteVolumeMassComplement site₀ site₁ site₂) =>
        observable
          (finiteVolumePositiveMassReconstruction
            site₀ site₁ site₂ state))
      (iidMassTripleLaw.prod
        (iidFiniteMassVectorLaw
          (finiteVolumeMassComplement site₀ site₁ site₂)))) :
    ∫⁻ omega,
        observable (ensemble.restrictPositiveMass (N := N) omega)
        ∂ensemble.probability =
      ∫⁻ state,
        observable
          (finiteVolumePositiveMassReconstruction
            site₀ site₁ site₂ state)
        ∂(iidMassTripleLaw.prod
          (iidFiniteMassVectorLaw
            (finiteVolumeMassComplement site₀ site₁ site₂))) := by
  have hval₀₁ : site₀.val ≠ site₁.val := by
    intro hval
    exact h₀₁ (ZMod.val_injective N hval)
  have hval₀₂ : site₀.val ≠ site₂.val := by
    intro hval
    exact h₀₂ (ZMod.val_injective N hval)
  have hval₁₂ : site₁.val ≠ site₂.val := by
    intro hval
    exact h₁₂ (ZMod.val_injective N hval)
  let rest := finiteVolumeMassComplement site₀ site₁ site₂
  have hsite₀Rest : site₀.val ∉ rest := by
    simp [rest, finiteVolumeMassComplement, selectedMassIndices]
  have hsite₁Rest : site₁.val ∉ rest := by
    simp [rest, finiteVolumeMassComplement, selectedMassIndices]
  have hsite₂Rest : site₂.val ∉ rest := by
    simp [rest, finiteVolumeMassComplement, selectedMassIndices]
  have hresampling :=
    lintegral_massTriple_finiteEnvironment_eq_prod
      ensemble hval₀₁ hval₀₂ hval₁₂ rest
        hsite₀Rest hsite₁Rest hsite₂Rest hmeasurable
  calc
    ∫⁻ omega,
        observable (ensemble.restrictPositiveMass (N := N) omega)
        ∂ensemble.probability =
      ∫⁻ omega,
        observable
          (finiteVolumePositiveMassReconstruction
            site₀ site₁ site₂
            (ensembleMassTriple ensemble
              site₀.val site₁.val site₂.val omega,
              ensembleFiniteMassVector ensemble rest omega))
        ∂ensemble.probability := by
      apply lintegral_congr
      intro omega
      exact congrArg observable
          (finiteVolumePositiveMassReconstruction_ensemble_eq
            ensemble site₀ site₁ site₂ omega).symm
    _ = ∫⁻ state,
        observable
          (finiteVolumePositiveMassReconstruction
            site₀ site₁ site₂ state)
        ∂(iidMassTripleLaw.prod
          (iidFiniteMassVectorLaw rest)) := hresampling

end

end ArchonPhysics.IIDMassTripleFiniteVolumeReconstruction
