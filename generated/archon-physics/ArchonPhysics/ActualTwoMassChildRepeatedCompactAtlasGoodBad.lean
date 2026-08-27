import ArchonPhysics.ActualTwoMassCountableSpectralAtlas
import ArchonPhysics.TwoParameterSpectralAveragingDensityUpper

/-!
# Compact finite atlases for actual two-mass child-frequency charts

A compact subset of the genuine simple-positive nondegenerate source is
covered by finitely many actual inverse-function patches.  The quantitative
area estimate is glued over those patches, replacing the unnecessarily strong
assumption that one global good set is injective.
-/

namespace ArchonPhysics.ActualTwoMassChildRepeatedCompactAtlasGoodBad

open ArchonPhysics
open ArchonPhysics.ActualTwoMassCountableSpectralAtlas
open ArchonPhysics.ActualTwoMassRegularSpectralPatch
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralAveragingDensityUpper
open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- A compact quantitative-good subset of one actual two-mass chart admits a
finite inverse-function atlas.  Its good pushforward has the expected summed
reciprocal-Jacobian bound; the weighted source outside the compact set is
retained exactly. -/
theorem exists_atlasCard_actualTwoMass_boundedDensity_frequencyPair_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (child₁ child₂ : Fin (Fintype.card (Lattice.Site N)))
    (weight : Real × Real → ENNReal) (weightCeiling : ENNReal)
    (hweight : ∀ᵐ point ∂iidMassPairLaw, weight point ≤ weightCeiling)
    (K : Set (Real × Real)) (hK : IsCompact K)
    (hKregular : K ⊆ actualTwoMassRegularSource
      fixed site₁ site₂ child₁ child₂)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ K,
      detLower ≤
        |(actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ child₁ child₂ point).det|) :
    ∃ atlasCard : Nat, ∀ {target : Set (Real × Real)},
      MeasurableSet target →
      Measure.map
          (actualTwoMassChildFrequencyChart
            fixed site₁ site₂ child₁ child₂)
          (iidMassPairLaw.withDensity weight) target ≤
        ((atlasCard : ENNReal) *
            (weightCeiling * 9 *
              (ENNReal.ofReal detLower)⁻¹)) *
            (volume : Measure (Real × Real)) target +
          (iidMassPairLaw.withDensity weight) Kᶜ := by
  classical
  let chart := actualTwoMassChildFrequencyChart
    fixed site₁ site₂ child₁ child₂
  let jacobian : (Real × Real) → (Real × Real) →L[Real] (Real × Real) :=
    actualTwoMassChildFrequencyJacobian
      fixed site₁ site₂ child₁ child₂
  let source : Measure (Real × Real) := iidMassPairLaw.withDensity weight
  have hchart : Measurable chart :=
    (continuous_actualTwoMassChildFrequencyChart
      fixed site₁ site₂ child₁ child₂).measurable
  have hKmeasurable : MeasurableSet K := hK.isClosed.measurableSet
  have hlocalPatch : ∀ point : K, ∃ patch : Set (Real × Real),
      IsOpen patch ∧ point.1 ∈ patch ∧ InjOn chart patch := by
    intro point
    have hregular := hKregular point.2
    obtain ⟨patch, hpoint, hopen, _hmeasurable, _hsupport,
        _hdifferentiable, hinjective⟩ :=
      exists_actualTwoMassChildFrequency_regularPatch_of_simpleSpectrum
        fixed hsite child₁ child₂ point.1 hregular.1 hregular.2.1
          hregular.2.2.1 hregular.2.2.2.1 hregular.2.2.2.2
    exact ⟨patch, hopen, hpoint, hinjective⟩
  choose patch hopen hmem hinjective using hlocalPatch
  obtain ⟨atlas, hcover⟩ := hK.elim_finite_subcover patch hopen (by
    intro point hpoint
    rw [mem_iUnion]
    exact ⟨⟨point, hpoint⟩, hmem ⟨point, hpoint⟩⟩)
  let AtlasIndex := {point : K // point ∈ atlas}
  let atlasPatch : AtlasIndex → Set (Real × Real) := fun index ↦
    K ∩ patch index.1
  have hatlasPatchMeasurable : ∀ index : AtlasIndex,
      MeasurableSet (atlasPatch index) := by
    intro index
    exact hKmeasurable.inter (hopen index.1).measurableSet
  have hK_eq : K = ⋃ index : AtlasIndex, atlasPatch index := by
    apply Subset.antisymm
    · intro point hpoint
      rcases mem_iUnion₂.mp (hcover hpoint) with
        ⟨center, hcenter, hpointPatch⟩
      rw [mem_iUnion]
      exact ⟨⟨center, hcenter⟩, hpoint, hpointPatch⟩
    · intro point hpoint
      rcases mem_iUnion.mp hpoint with ⟨index, hindex⟩
      exact hindex.1
  have hderivative : ∀ index : AtlasIndex, ∀ point ∈ atlasPatch index,
      HasFDerivWithinAt chart (jacobian point) (atlasPatch index) point := by
    intro index point hpoint
    have hregular := hKregular hpoint.1
    obtain ⟨derivative, hstrict⟩ :=
      exists_hasStrictFDerivAt_actualTwoMassChildFrequencyChart
        fixed hsite hregular.1 hregular.2.1 child₁ child₂
          hregular.2.2.1 hregular.2.2.2.1
    have hjacobian : jacobian point = derivative := by
      simpa [jacobian, actualTwoMassChildFrequencyJacobian, chart] using
        hstrict.hasFDerivAt.fderiv
    rw [hjacobian]
    exact hstrict.hasFDerivAt.hasFDerivWithinAt
  have hsourceIID : source ≤ weightCeiling • iidMassPairLaw := by
    calc
      source ≤ iidMassPairLaw.withDensity (fun _ ↦ weightCeiling) :=
        withDensity_mono hweight
      _ = weightCeiling • iidMassPairLaw :=
        withDensity_const weightCeiling
  have hsourceVolume : source ≤
      (weightCeiling * 9) • (volume : Measure (Real × Real)) := by
    calc
      source ≤ weightCeiling • iidMassPairLaw := hsourceIID
      _ ≤ weightCeiling •
          ((9 : ENNReal) • (volume : Measure (Real × Real))) :=
        smul_mono_right weightCeiling iidMassPairLaw_le_nine_smul_volume
      _ = (weightCeiling * 9) •
          (volume : Measure (Real × Real)) := by rw [mul_smul]
  have hlocalMap : ∀ index : AtlasIndex,
      Measure.map chart (source.restrict (atlasPatch index)) ≤
        (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) •
          (volume : Measure (Real × Real)) := by
    intro index
    have hsourcePatch : source.restrict (atlasPatch index) ≤
        (weightCeiling * 9) •
          (volume : Measure (Real × Real)).restrict (atlasPatch index) := by
      calc
        source.restrict (atlasPatch index) ≤
            ((weightCeiling * 9) •
              (volume : Measure (Real × Real))).restrict
                (atlasPatch index) :=
          Measure.restrict_mono_measure hsourceVolume _
        _ = (weightCeiling * 9) •
            (volume : Measure (Real × Real)).restrict
              (atlasPatch index) := by rw [Measure.restrict_smul]
    exact map_le_smul_volume_of_le_volume_restrict_of_det_lower
      (volume : Measure (Real × Real)) (hatlasPatchMeasurable index)
      chart hchart jacobian (hderivative index)
      ((hinjective index.1).mono inter_subset_right)
      hdetLower (fun point hpoint ↦ hdet point hpoint.1)
      (source.restrict (atlasPatch index)) (weightCeiling * 9)
      hsourcePatch
  have hrestrictK : source.restrict K ≤
      Measure.sum fun index : AtlasIndex ↦
        source.restrict (atlasPatch index) := by
    rw [hK_eq]
    exact Measure.restrict_iUnion_le
  have hmapK : Measure.map chart (source.restrict K) ≤
      Measure.sum fun index : AtlasIndex ↦
        Measure.map chart (source.restrict (atlasPatch index)) := by
    calc
      Measure.map chart (source.restrict K) ≤
          Measure.map chart (Measure.sum fun index : AtlasIndex ↦
            source.restrict (atlasPatch index)) :=
        Measure.map_mono hrestrictK hchart
      _ = Measure.sum fun index : AtlasIndex ↦
          Measure.map chart (source.restrict (atlasPatch index)) := by
        rw [Measure.map_sum hchart.aemeasurable]
  have hsum :
      (Measure.sum fun index : AtlasIndex ↦
        Measure.map chart (source.restrict (atlasPatch index))) ≤
      ((Fintype.card AtlasIndex : ENNReal) *
        (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹)) •
          (volume : Measure (Real × Real)) := by
    rw [Measure.le_iff]
    intro measurableSet hmeasurableSet
    rw [Measure.sum_apply _ hmeasurableSet, Measure.smul_apply]
    simp only [tsum_fintype, smul_eq_mul]
    calc
      (∑ index : AtlasIndex,
          Measure.map chart (source.restrict (atlasPatch index))
            measurableSet) ≤
        ∑ _index : AtlasIndex,
          (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
            (volume : Measure (Real × Real)) measurableSet :=
        Finset.sum_le_sum fun index _hindex ↦ hlocalMap index measurableSet
      _ = (Fintype.card AtlasIndex : ENNReal) *
          (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹) *
            (volume : Measure (Real × Real)) measurableSet := by
        simp [mul_assoc]
  have hgoodMap : Measure.map chart (source.restrict K) ≤
      ((Fintype.card AtlasIndex : ENNReal) *
        (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹)) •
          (volume : Measure (Real × Real)) := hmapK.trans hsum
  refine ⟨atlas.card, ?_⟩
  intro target htarget
  have hsplit : Measure.map chart source =
      Measure.map chart (source.restrict K) +
        Measure.map chart (source.restrict Kᶜ) := by
    rw [← Measure.map_add _ _ hchart,
      source.restrict_add_restrict_compl hKmeasurable]
  have hbadApply :
      Measure.map chart (source.restrict Kᶜ) target ≤ source Kᶜ := by
    rw [Measure.map_apply hchart htarget,
      Measure.restrict_apply (htarget.preimage hchart)]
    exact measure_mono inter_subset_right
  rw [hsplit, Measure.add_apply]
  calc
    Measure.map chart (source.restrict K) target +
        Measure.map chart (source.restrict Kᶜ) target ≤
      ((Fintype.card AtlasIndex : ENNReal) *
          (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹)) *
          (volume : Measure (Real × Real)) target +
        Measure.map chart (source.restrict Kᶜ) target := by
      gcongr
      simpa only [Measure.smul_apply, smul_eq_mul] using hgoodMap target
    _ ≤ ((Fintype.card AtlasIndex : ENNReal) *
          (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹)) *
          (volume : Measure (Real × Real)) target + source Kᶜ := by
      exact add_le_add (le_refl _) hbadApply
    _ = ((atlas.card : ENNReal) *
          (weightCeiling * 9 * (ENNReal.ofReal detLower)⁻¹)) *
          (volume : Measure (Real × Real)) target +
        (iidMassPairLaw.withDensity weight) Kᶜ := by
      simp [AtlasIndex, source]

end


end ArchonPhysics.ActualTwoMassChildRepeatedCompactAtlasGoodBad
