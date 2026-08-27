import ArchonPhysics.ActualThreeMassLiftedCompactAtlasGoodBad
import ArchonPhysics.ActualThreeMassLiftedJacobianContinuity

/-!
# Automatic quantitative atlases on compact actual regular sectors

Compactness and the exact actual-Jacobian continuity theorem automatically
produce a positive determinant threshold.  Combining it with finite IFT
atlas extraction removes both the global-injectivity and determinant-lower
hypotheses on every fixed compact subset of the true regular source.
-/

namespace ArchonPhysics.ActualThreeMassLiftedCompactRegularAtlas

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedCompactAtlasGoodBad
open ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A compact genuine regular sector automatically admits both a positive
true-Jacobian threshold and a finite quantitative atlas. -/
theorem exists_detLower_atlasCard_actualThreeMassLifted_weightedSource_broadenedChild_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (source : Measure MassTriple) (sourceCeiling : ENNReal)
    (hsource : source ≤ sourceCeiling • iidMassTripleLaw)
    (K : Set MassTriple) (hK : IsCompact K)
    (hKregular : K ⊆ actualThreeMassProjectorRegularSource
      fixed site₀ site₁ site₂ modes)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    ∃ detLower : Real, ∃ atlasCard : Nat,
      0 < detLower ∧
      Measure.map Prod.fst
          ((Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            source).withDensity
              (liftedResonanceKernelDensity T)) target ≤
        ((atlasCard : ENNReal) *
            (sourceCeiling * 27 *
              (ENNReal.ofReal detLower)⁻¹)) *
            (volume : Measure (Real × Real)) target +
          (Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            (source.restrict Kᶜ)).withDensity
              (liftedResonanceKernelDensity T) univ := by
  obtain ⟨detLower, hdetLower, hdet⟩ :=
    exists_positive_actualThreeMassLiftedJacobian_detLower_on_compact
      fixed h₁₀ h₂₀ h₂₁ sign modes K hK hKregular
  obtain ⟨atlasCard, hbound⟩ :=
    exists_atlasCard_actualThreeMassLifted_weightedSource_broadenedChild_apply_le
      fixed h₁₀ h₂₀ h₂₁ sign modes source sourceCeiling hsource
        K hK hKregular hdetLower hdet hT htarget
  exact ⟨detLower, atlasCard, hdetLower, hbound⟩

/-- Bounded collision-density specialization of automatic compact actual
atlas extraction. -/
theorem exists_detLower_atlasCard_actualThreeMassLifted_boundedDensity_broadenedChild_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (weight : MassTriple → ENNReal) (weightCeiling : ENNReal)
    (hweight : ∀ᵐ point ∂iidMassTripleLaw,
      weight point ≤ weightCeiling)
    (K : Set MassTriple) (hK : IsCompact K)
    (hKregular : K ⊆ actualThreeMassProjectorRegularSource
      fixed site₀ site₁ site₂ modes)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    ∃ detLower : Real, ∃ atlasCard : Nat,
      0 < detLower ∧
      Measure.map Prod.fst
          ((Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            (iidMassTripleLaw.withDensity weight)).withDensity
              (liftedResonanceKernelDensity T)) target ≤
        ((atlasCard : ENNReal) *
            (weightCeiling * 27 *
              (ENNReal.ofReal detLower)⁻¹)) *
            (volume : Measure (Real × Real)) target +
          (Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            ((iidMassTripleLaw.withDensity weight).restrict Kᶜ)).withDensity
              (liftedResonanceKernelDensity T) univ := by
  apply exists_detLower_atlasCard_actualThreeMassLifted_weightedSource_broadenedChild_apply_le
    fixed h₁₀ h₂₀ h₂₁ sign modes
    (iidMassTripleLaw.withDensity weight) weightCeiling
  · calc
      iidMassTripleLaw.withDensity weight ≤
          iidMassTripleLaw.withDensity (fun _ => weightCeiling) :=
        withDensity_mono hweight
      _ = weightCeiling • iidMassTripleLaw :=
        withDensity_const weightCeiling
  · exact hK
  · exact hKregular
  · exact hT
  · exact htarget

end

end ArchonPhysics.ActualThreeMassLiftedCompactRegularAtlas
