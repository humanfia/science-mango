import ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch
import ArchonPhysics.ActualThreeMassLiftedWeightedSourceGoodBad
import ArchonPhysics.ActualThreeMassProjectorMinorRegularity

/-!
# Compact finite atlases for the actual lifted three-mass chart

On an arbitrary compact subset of the genuine simple-positive regular
source, the actual inverse-function patches admit a finite subcover.  The
quantitative Jacobian estimate can therefore be glued before the normalized
resonance kernel is inserted.  The resulting theorem removes a user-supplied
single global injective patch: the only geometric cost is the cardinality of
the extracted finite atlas.

This is a fixed-volume existence theorem.  It deliberately does not claim a
uniform bound on the atlas cardinal as the lattice volume changes, and it
keeps the sinc-squared-weighted complement exactly.
-/

namespace ArchonPhysics.ActualThreeMassLiftedCompactAtlasGoodBad

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance tripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- A compact subset of the genuine actual regular source has a finite
quantitative atlas.  The good part is bounded by `atlasCard` times the
one-chart reciprocal-Jacobian constant, while the complement remains with
its exact normalized sinc-squared weight. -/
theorem exists_atlasCard_actualThreeMassLifted_weightedSource_broadenedChild_apply_le
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
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ K,
      detLower ≤
        |(actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point).det|)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    ∃ atlasCard : Nat,
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
  classical
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  let jacobian : MassTriple → MassTriple →L[Real] MassTriple :=
    actualThreeMassLiftedFrequencyJacobian
      fixed site₀ site₁ site₂ sign modes
  have hchart : Measurable chart :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  have hKmeasurable : MeasurableSet K := hK.isClosed.measurableSet
  have hlocalPatch : ∀ point : K, ∃ patch : Set MassTriple,
      IsOpen patch ∧ point.1 ∈ patch ∧ InjOn chart patch := by
    intro point
    have hregular := hKregular point.2
    have hlifted :=
      (mem_actualThreeMassProjectorRegularSource_iff_lifted
        fixed h₁₀ h₂₀ h₂₁ sign modes point.1).1 hregular
    obtain ⟨patch, hpoint, hopen, _hmeasurable, _hsupport,
        _hdifferentiable, hinjective⟩ :=
      exists_actualThreeMassLiftedFrequency_regularPatch_of_simpleSpectrum
        fixed h₁₀ h₂₀ h₂₁ sign modes point.1 hlifted.1
          hlifted.2.1 hlifted.2.2.1 hlifted.2.2.2
    exact ⟨patch, hopen, hpoint, hinjective⟩
  choose patch hopen hmem hinjective using hlocalPatch
  obtain ⟨atlas, hcover⟩ := hK.elim_finite_subcover patch hopen (by
    intro point hpoint
    rw [mem_iUnion]
    exact ⟨⟨point, hpoint⟩, hmem ⟨point, hpoint⟩⟩)
  let AtlasIndex := {point : K // point ∈ atlas}
  let atlasPatch : AtlasIndex → Set MassTriple := fun index =>
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
      exists_hasStrictFDerivAt_actualThreeMassLiftedFrequencyChart
        fixed h₁₀ h₂₀ h₂₁ sign modes hregular.1 hregular.2.1
          hregular.2.2.1
    have hjacobian : jacobian point = derivative := by
      simpa [jacobian, actualThreeMassLiftedFrequencyJacobian, chart] using
        hstrict.hasFDerivAt.fderiv
    rw [hjacobian]
    exact hstrict.hasFDerivAt.hasFDerivWithinAt
  have hsourceVolume : source ≤
      (sourceCeiling * 27) • (volume : Measure MassTriple) := by
    calc
      source ≤ sourceCeiling • iidMassTripleLaw := hsource
      _ ≤ sourceCeiling •
          ((27 : ENNReal) • (volume : Measure MassTriple)) :=
        smul_mono_right sourceCeiling
          iidMassTripleLaw_le_twentySeven_smul_volume
      _ = (sourceCeiling * 27) • (volume : Measure MassTriple) := by
        rw [mul_smul]
  have hlocalMap : ∀ index : AtlasIndex,
      Measure.map chart (source.restrict (atlasPatch index)) ≤
        (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) •
          (volume : Measure MassTriple) := by
    intro index
    have hsourcePatch : source.restrict (atlasPatch index) ≤
        (sourceCeiling * 27) •
          (volume : Measure MassTriple).restrict (atlasPatch index) := by
      calc
        source.restrict (atlasPatch index) ≤
            ((sourceCeiling * 27) •
              (volume : Measure MassTriple)).restrict (atlasPatch index) :=
          Measure.restrict_mono_measure hsourceVolume _
        _ = (sourceCeiling * 27) •
            (volume : Measure MassTriple).restrict (atlasPatch index) := by
          rw [Measure.restrict_smul]
    exact map_le_smul_volume_of_le_volume_restrict_of_det_lower
      (volume : Measure MassTriple) (hatlasPatchMeasurable index)
      chart hchart jacobian (hderivative index)
      ((hinjective index.1).mono inter_subset_right)
      hdetLower (fun point hpoint => hdet point hpoint.1)
      (source.restrict (atlasPatch index)) (sourceCeiling * 27)
      hsourcePatch
  have hrestrictK : source.restrict K ≤
      Measure.sum fun index : AtlasIndex =>
        source.restrict (atlasPatch index) := by
    rw [hK_eq]
    exact Measure.restrict_iUnion_le
  have hmapK : Measure.map chart (source.restrict K) ≤
      Measure.sum fun index : AtlasIndex =>
        Measure.map chart (source.restrict (atlasPatch index)) := by
    calc
      Measure.map chart (source.restrict K) ≤
          Measure.map chart (Measure.sum fun index : AtlasIndex =>
            source.restrict (atlasPatch index)) :=
        Measure.map_mono hrestrictK hchart
      _ = Measure.sum fun index : AtlasIndex =>
          Measure.map chart (source.restrict (atlasPatch index)) := by
        rw [Measure.map_sum hchart.aemeasurable]
  have hsum :
      (Measure.sum fun index : AtlasIndex =>
        Measure.map chart (source.restrict (atlasPatch index))) ≤
      ((Fintype.card AtlasIndex : ENNReal) *
        (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹)) •
          (volume : Measure MassTriple) := by
    rw [Measure.le_iff]
    intro measurableSet hmeasurableSet
    rw [Measure.sum_apply _ hmeasurableSet, Measure.smul_apply]
    simp only [tsum_fintype, smul_eq_mul]
    calc
      (∑ index : AtlasIndex,
          Measure.map chart (source.restrict (atlasPatch index))
            measurableSet) ≤
          ∑ _index : AtlasIndex,
            (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
              (volume : Measure MassTriple) measurableSet :=
        Finset.sum_le_sum fun index _hindex =>
          hlocalMap index measurableSet
      _ = (Fintype.card AtlasIndex : ENNReal) *
          (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
            (volume : Measure MassTriple) measurableSet := by
        simp [mul_assoc]
  have hgoodLifted : Measure.map chart (source.restrict K) ≤
      ((Fintype.card AtlasIndex : ENNReal) *
        (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹)) •
          (volume : Measure MassTriple) := hmapK.trans hsum
  have hsplit : Measure.map chart source =
      Measure.map chart (source.restrict K) +
        Measure.map chart (source.restrict Kᶜ) := by
    rw [← Measure.map_add _ _ hchart,
      source.restrict_add_restrict_compl hKmeasurable]
  have hbound := map_fst_withDensity_good_add_bad_apply_le
    (Measure.map chart (source.restrict K))
    (Measure.map chart (source.restrict Kᶜ)) hT
    ((Fintype.card AtlasIndex : ENNReal) *
      (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹))
    hgoodLifted htarget
  rw [hsplit]
  refine ⟨atlas.card, ?_⟩
  simpa [AtlasIndex, chart] using hbound

/-- Bounded-density specialization for the actual collision-weighted iid
triple source. -/
theorem exists_atlasCard_actualThreeMassLifted_boundedDensity_broadenedChild_apply_le
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
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ K,
      detLower ≤
        |(actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point).det|)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    ∃ atlasCard : Nat,
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
  apply exists_atlasCard_actualThreeMassLifted_weightedSource_broadenedChild_apply_le
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
  · exact hdetLower
  · exact hdet
  · exact hT
  · exact htarget

end

end ArchonPhysics.ActualThreeMassLiftedCompactAtlasGoodBad
