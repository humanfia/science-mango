import ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
import ArchonPhysics.ActualThreeMassLiftedCompactAtlasPerSiteScaling

/-!
# Automatic compact-atlas coarea for the actual all-distinct sector

The compact regular-atlas construction already supplies genuine inverse-
function patches for the actual three-mass lifted frequency chart.  This
module exposes the raw three-dimensional pushforward estimate that is used
inside the broadened theorem, and then sums those estimates over all ordered
mode triples with the canonical inverse-volume normalization.

For every fixed finite volume and every modewise compact subset of the true
regular source, no chart, injectivity, derivative, or Jacobian-lower-bound
hypothesis remains.  The resulting coarea constant is exactly the existing
normalized compact-atlas budget.  A thermodynamic theorem therefore reduces
to an explicit uniform ceiling for these genuine atlas budgets; compactness
alone does not prove that ceiling.
-/

namespace ArchonPhysics.ActualThreeMassAllDistinctJointCompactAtlasCoarea

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassAllDistinctJointCoareaOverlap
open ArchonPhysics.ActualThreeMassAllDistinctRegularGrowth
open ArchonPhysics.ActualThreeMassLiftedCompactAtlasPerSiteScaling
open ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
open ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance tripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- A compact subset of one genuine regular chart has a finite actual IFT
atlas whose raw three-dimensional pushforward is Lebesgue dominated.  This
is the raw endpoint hidden inside the compact-atlas broadening proof. -/
theorem exists_atlasCard_actualThreeMassLifted_weightedSource_restrict_map_le
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
          fixed site₀ site₁ site₂ sign modes point).det|) :
    ∃ atlasCard : Nat,
      Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          (source.restrict K) ≤
        ((atlasCard : ENNReal) *
          (sourceCeiling * 27 *
            (ENNReal.ofReal detLower)⁻¹)) •
          (volume : Measure MassTriple) := by
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
    intro target htarget
    rw [Measure.sum_apply _ htarget, Measure.smul_apply]
    simp only [tsum_fintype, smul_eq_mul]
    calc
      (∑ index : AtlasIndex,
          Measure.map chart (source.restrict (atlasPatch index)) target) ≤
        ∑ _index : AtlasIndex,
          (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
            (volume : Measure MassTriple) target :=
        Finset.sum_le_sum fun index _hindex => hlocalMap index target
      _ = (Fintype.card AtlasIndex : ENNReal) *
          (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
            (volume : Measure MassTriple) target := by
        simp [mul_assoc]
  refine ⟨atlas.card, ?_⟩
  simpa [AtlasIndex, chart] using hmapK.trans hsum

/-- Compactness and actual Jacobian continuity automatically select the
positive determinant threshold as well as the finite raw atlas. -/
theorem exists_detLower_atlasCard_actualThreeMassLifted_weightedSource_restrict_map_le
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
      fixed site₀ site₁ site₂ modes) :
    ∃ detLower : Real, ∃ atlasCard : Nat,
      0 < detLower ∧
      Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          (source.restrict K) ≤
        ((atlasCard : ENNReal) *
          (sourceCeiling * 27 *
            (ENNReal.ofReal detLower)⁻¹)) •
          (volume : Measure MassTriple) := by
  obtain ⟨detLower, hdetLower, hdet⟩ :=
    exists_positive_actualThreeMassLiftedJacobian_detLower_on_compact
      fixed h₁₀ h₂₀ h₂₁ sign modes K hK hKregular
  obtain ⟨atlasCard, hbound⟩ :=
    exists_atlasCard_actualThreeMassLifted_weightedSource_restrict_map_le
      fixed h₁₀ h₂₀ h₂₁ sign modes source sourceCeiling hsource
        K hK hKregular hdetLower hdet
  exact ⟨detLower, atlasCard, hdetLower, hbound⟩

/-- Every modewise compact subset of the genuine all-distinct regular source
has an actual joint coarea bound.  Its coefficient is the exact normalized
sum of the automatically extracted atlas-cardinality and reciprocal-
Jacobian costs. -/
theorem exists_actualThreeMassAllDistinctJointCompactAtlasCoareaBound
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (K : OrderedModeTriple N → Set MassTriple)
    (hKcompact : ∀ modes, IsCompact (K modes))
    (hKregular : ∀ modes, K modes ⊆
      actualThreeMassProjectorRegularSource
        fixed site₀ site₁ site₂ modes) :
    ∃ detLower : OrderedModeTriple N → Real,
      ∃ atlasCard : OrderedModeTriple N → Nat,
        (∀ modes, 0 < detLower modes) ∧
        actualThreeMassAllDistinctJointGoodCoareaBound
          fixed site₀ site₁ site₂ sign K
          (actualThreeMassAtlasRegularPerSiteBudget atlasCard
            (fun _ => ENNReal.ofReal
              (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
            detLower) := by
  classical
  let sourceCeiling : ENNReal := ENNReal.ofReal
    (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8)
  have hlocal : ∀ modes : OrderedModeTriple N,
      ∃ detLower : Real, ∃ atlasCard : Nat,
        0 < detLower ∧
        Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            ((iidMassTripleLaw.withDensity
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes)).restrict (K modes)) ≤
          ((atlasCard : ENNReal) *
            (sourceCeiling * 27 *
              (ENNReal.ofReal detLower)⁻¹)) •
            (volume : Measure MassTriple) := by
    intro modes
    apply
      exists_detLower_atlasCard_actualThreeMassLifted_weightedSource_restrict_map_le
        fixed h₁₀ h₂₀ h₂₁ sign modes
        (iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes)) sourceCeiling
    · calc
        iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes) ≤
          iidMassTripleLaw.withDensity (fun _ => sourceCeiling) :=
            withDensity_mono (ae_of_all _ fun triple =>
              actualThreeMassAllDistinctTupleWeight_le_acousticCeiling
                fixed hfixed site₀ site₁ site₂ modes triple)
        _ = sourceCeiling • iidMassTripleLaw :=
          withDensity_const sourceCeiling
    · exact hKcompact modes
    · exact hKregular modes
  choose detLower atlasCard hdetLower hlocalBound using hlocal
  refine ⟨detLower, atlasCard, hdetLower, ?_⟩
  unfold actualThreeMassAllDistinctJointGoodCoareaBound
    actualThreeMassAllDistinctJointGoodLiftedMeasure
  rw [Measure.le_iff]
  intro target htarget
  rw [Measure.smul_apply, Measure.coe_finsetSum, Measure.smul_apply]
  simp only [Finset.sum_apply, smul_eq_mul]
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            ((iidMassTripleLaw.withDensity
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes)).restrict (K modes)) target ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          ((atlasCard modes : ENNReal) *
            (sourceCeiling * 27 *
              (ENNReal.ofReal (detLower modes))⁻¹)) *
            (volume : Measure MassTriple) target := by
      exact mul_le_mul_right
        (Finset.sum_le_sum fun modes _hmodes => hlocalBound modes target) _
    _ = actualThreeMassAtlasRegularPerSiteBudget atlasCard
          (fun _ => ENNReal.ofReal
            (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
          detLower * (volume : Measure MassTriple) target := by
      unfold actualThreeMassAtlasRegularPerSiteBudget sourceCeiling
      rw [← Finset.sum_mul]
      ring

/-- Once the explicit actual compact-atlas budget has a ceiling `C`, the
same good law is dominated by `C * volume`.  This is the precise scalar
thermodynamic input left after all local model geometry has been proved. -/
theorem actualThreeMassAllDistinctJointGoodCoareaBound_mono_budget
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (K : OrderedModeTriple N → Set MassTriple)
    {atlasCard : OrderedModeTriple N → Nat}
    {detLower : OrderedModeTriple N → Real}
    {C : ENNReal}
    (hcoarea : actualThreeMassAllDistinctJointGoodCoareaBound
      fixed site₀ site₁ site₂ sign K
        (actualThreeMassAtlasRegularPerSiteBudget atlasCard
          (fun _ => ENNReal.ofReal
            (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
          detLower))
    (hbudget : actualThreeMassAtlasRegularPerSiteBudget atlasCard
        (fun _ => ENNReal.ofReal
          (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
        detLower ≤ C) :
    actualThreeMassAllDistinctJointGoodCoareaBound
      fixed site₀ site₁ site₂ sign K C := by
  unfold actualThreeMassAllDistinctJointGoodCoareaBound at hcoarea ⊢
  refine hcoarea.trans ?_
  rw [Measure.le_iff]
  intro target htarget
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left hbudget _

/-- Consumer-facing form of the reduction.  The actual model constructs all
finite-volume geometric data.  To use one constant `C` across volumes, the
only remaining premise is the displayed scalar ceiling for the constructed
normalized atlas budget. -/
theorem exists_actualThreeMassAllDistinctJointCompactAtlasCoareaBound_of_budgetCeiling
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (hfixed : ∀ site, fixed.mass site ∈ massSupport)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (K : OrderedModeTriple N → Set MassTriple)
    (hKcompact : ∀ modes, IsCompact (K modes))
    (hKregular : ∀ modes, K modes ⊆
      actualThreeMassProjectorRegularSource
        fixed site₀ site₁ site₂ modes) :
    ∃ detLower : OrderedModeTriple N → Real,
      ∃ atlasCard : OrderedModeTriple N → Nat,
        (∀ modes, 0 < detLower modes) ∧
        ∀ {C : ENNReal},
          actualThreeMassAtlasRegularPerSiteBudget atlasCard
              (fun _ => ENNReal.ofReal
                (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
              detLower ≤ C →
            actualThreeMassAllDistinctJointGoodCoareaBound
              fixed site₀ site₁ site₂ sign K C := by
  obtain ⟨detLower, atlasCard, hdetLower, hcoarea⟩ :=
    exists_actualThreeMassAllDistinctJointCompactAtlasCoareaBound
      fixed hfixed h₁₀ h₂₀ h₂₁ sign K hKcompact hKregular
  refine ⟨detLower, atlasCard, hdetLower, ?_⟩
  intro C hbudget
  exact actualThreeMassAllDistinctJointGoodCoareaBound_mono_budget
    fixed site₀ site₁ site₂ sign K hcoarea hbudget

/-- Cross-volume frozen-sequence form.  All finite-volume atlas witnesses
are selected from the actual harmonic charts.  A single scalar upper bound
on their normalized costs then yields the same joint coarea constant at
every volume `n + 3`. -/
theorem exists_actualThreeMassAllDistinctFrozenSequenceJointCoareaBound_of_uniformCompactAtlasBudget
    (fixed : (n : Nat) → Lattice.PositiveMassConfig (n + 3))
    (hfixed : ∀ n site, (fixed n).mass site ∈ massSupport)
    (site₀ site₁ site₂ : (n : Nat) → Lattice.Site (n + 3))
    (h₁₀ : ∀ n, site₁ n ≠ site₀ n)
    (h₂₀ : ∀ n, site₂ n ≠ site₀ n)
    (h₂₁ : ∀ n, site₂ n ≠ site₁ n)
    (sign : Fin 3 → InteractionSign)
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
            ∀ n,
              actualThreeMassAllDistinctJointGoodCoareaBound
                (fixed n) (site₀ n) (site₁ n) (site₂ n) sign (K n) C := by
  have hvolume : ∀ n,
      ∃ detLower : OrderedModeTriple (n + 3) → Real,
        ∃ atlasCard : OrderedModeTriple (n + 3) → Nat,
          (∀ modes, 0 < detLower modes) ∧
          ∀ {C : ENNReal},
            actualThreeMassAtlasRegularPerSiteBudget atlasCard
                (fun _ => ENNReal.ofReal
                  (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8))
                detLower ≤ C →
              actualThreeMassAllDistinctJointGoodCoareaBound
                (fixed n) (site₀ n) (site₁ n) (site₂ n) sign (K n) C := by
    intro n
    exact
      exists_actualThreeMassAllDistinctJointCompactAtlasCoareaBound_of_budgetCeiling
        (fixed n) (hfixed n) (h₁₀ n) (h₂₀ n) (h₂₁ n)
        sign (K n) (hKcompact n) (hKregular n)
  choose detLower atlasCard hdetLower hcoarea using hvolume
  refine ⟨detLower, atlasCard, hdetLower, ?_⟩
  intro C hbudget n
  exact hcoarea n (hbudget n)

end

end ArchonPhysics.ActualThreeMassAllDistinctJointCompactAtlasCoarea
