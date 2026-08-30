import ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
import ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
import ArchonPhysics.QuantitativeJacobianGoodBadPushforward

/-!
# Compact actual pair-fiber atlases give quantitative A1 small balls

The actual one-mass mismatch chart is only locally injective away from its
critical set.  This module turns those local inverse-function patches into a
finite quantitative atlas on an explicitly supplied compact set `K`.

The assumptions on `K` are deliberately visible: it must lie in the actual
interior simple-spectrum positive-frequency source, and the genuine vertical
Jacobian must satisfy `j₀ ≤ |J|` on `K` for a displayed `j₀ > 0`.
Compactness selects finitely many local injectivity patches.  Consequently
the regular contribution is bounded by

`atlasCard * (5/2) * j₀⁻¹ * volume(target)`,

while the full scalar law retains exactly `massCoordinateLaw Kᶜ`.

An abstract finite-atlas theorem first keeps every patch density and Jacobian
lower bound separate, so the multiplicity is the finite sum
`Σᵢ densityᵢ * jᵢ⁻¹`.  The final fixed-order theorem applies the
compact construction to a finite type containing only the ordinary
denominators and gives

`Σⱼ Cⱼ * ofReal (2 * δ) + P(⋃ⱼ Kⱼᶜ)`.

The complementary history indices are represented by an explicit retained
sector and are not estimated here.  In particular, genuine resonances,
charge-balanced blocks, and recollisions stay in that sector unless a
separate theorem removes them.  The identically resonant acoustic-copy A1
term is removable only because the preceding module proves its complete
interaction coefficient is exactly zero.  No phase independence, re-Haar,
Markov closure, or order-independent RPA conclusion occurs below.
-/

namespace ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.QuantitativeJacobianGoodBadPushforward
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Quantitative gluing for a finite scalar atlas.  Every patch has its own
source-density ceiling and its own positive Jacobian lower bound.  The first
conclusion controls the source restricted to `K`; the second adds exactly the
source mass outside `K`. -/
theorem scalarFinitePatchAtlas_map_restrict_and_full_apply_le
    {Index : Type*} [Fintype Index]
    (source : Measure Real) (K : Set Real) (hK : MeasurableSet K)
    (chart : Real → Real) (hchart : Measurable chart)
    (patch : Index → Set Real)
    (hpatch : ∀ index, MeasurableSet (patch index))
    (hcover : K ⊆ ⋃ index, patch index)
    (derivative : Index → Real → (Real →L[Real] Real))
    (hderivative : ∀ index point, point ∈ patch index →
      HasFDerivWithinAt chart (derivative index point)
        (patch index) point)
    (hinjective : ∀ index, InjOn chart (patch index))
    (jacLower : Index → Real) (hjacLower : ∀ index, 0 < jacLower index)
    (hjac : ∀ index point, point ∈ patch index →
      jacLower index ≤ |(derivative index point).det|)
    (sourceDensity : Index → ENNReal)
    (hsource : ∀ index, source.restrict (patch index) ≤
      sourceDensity index •
        (volume : Measure Real).restrict (patch index)) :
    (∀ {target : Set Real}, MeasurableSet target →
      Measure.map chart (source.restrict K) target ≤
        (∑ index, sourceDensity index *
          (ENNReal.ofReal (jacLower index))⁻¹) *
            (volume : Measure Real) target) ∧
    (∀ {target : Set Real}, MeasurableSet target →
      Measure.map chart source target ≤
        (∑ index, sourceDensity index *
          (ENNReal.ofReal (jacLower index))⁻¹) *
            (volume : Measure Real) target + source Kᶜ) := by
  classical
  have hlocalMap : ∀ index,
      Measure.map chart (source.restrict (patch index)) ≤
        (sourceDensity index *
          (ENNReal.ofReal (jacLower index))⁻¹) •
            (volume : Measure Real) := by
    intro index
    simpa using map_good_add_bad_le_density_smul_add_map_bad
      (volume : Measure Real) (hpatch index) chart hchart
      (derivative index) (hderivative index) (hinjective index)
      (hjacLower index) (hjac index)
      (source.restrict (patch index)) 0 (sourceDensity index)
      (hsource index)
  have hrestrictK : source.restrict K ≤
      Measure.sum fun index : Index => source.restrict (patch index) := by
    calc
      source.restrict K ≤ source.restrict (⋃ index, patch index) :=
        source.restrict_mono_set hcover
      _ ≤ Measure.sum fun index : Index =>
          source.restrict (patch index) := Measure.restrict_iUnion_le
  have hmapK : Measure.map chart (source.restrict K) ≤
      Measure.sum fun index : Index =>
        Measure.map chart (source.restrict (patch index)) := by
    calc
      Measure.map chart (source.restrict K) ≤
          Measure.map chart (Measure.sum fun index : Index =>
            source.restrict (patch index)) :=
        Measure.map_mono hrestrictK hchart
      _ = Measure.sum fun index : Index =>
          Measure.map chart (source.restrict (patch index)) := by
        rw [Measure.map_sum hchart.aemeasurable]
  have hregular : ∀ {target : Set Real}, MeasurableSet target →
      Measure.map chart (source.restrict K) target ≤
        (∑ index, sourceDensity index *
          (ENNReal.ofReal (jacLower index))⁻¹) *
            (volume : Measure Real) target := by
    intro target htarget
    calc
      Measure.map chart (source.restrict K) target ≤
          (Measure.sum fun index : Index =>
            Measure.map chart (source.restrict (patch index))) target :=
        hmapK target
      _ = ∑ index : Index,
          Measure.map chart (source.restrict (patch index)) target := by
        rw [Measure.sum_apply _ htarget]
        simp only [tsum_fintype]
      _ ≤ ∑ index : Index,
          (sourceDensity index *
            (ENNReal.ofReal (jacLower index))⁻¹) *
              (volume : Measure Real) target := by
        exact Finset.sum_le_sum fun index _ => hlocalMap index target
      _ = (∑ index, sourceDensity index *
          (ENNReal.ofReal (jacLower index))⁻¹) *
            (volume : Measure Real) target := by
        rw [Finset.sum_mul]
  refine ⟨hregular, ?_⟩
  intro target htarget
  have hsplit : Measure.map chart source =
      Measure.map chart (source.restrict K) +
        Measure.map chart (source.restrict Kᶜ) := by
    rw [← Measure.map_add _ _ hchart,
      source.restrict_add_restrict_compl hK]
  have hbad : Measure.map chart (source.restrict Kᶜ) target ≤
      source Kᶜ := by
    rw [Measure.map_apply hchart htarget,
      Measure.restrict_apply (htarget.preimage hchart)]
    exact measure_mono inter_subset_right
  rw [hsplit, Measure.add_apply]
  exact add_le_add (hregular htarget) hbad

/-- Centered-interval specialization of the finite scalar atlas. -/
theorem scalarFinitePatchAtlas_smallBall_le
    {Index : Type*} [Fintype Index]
    (source : Measure Real) (K : Set Real) (hK : MeasurableSet K)
    (chart : Real → Real) (hchart : Measurable chart)
    (patch : Index → Set Real)
    (hpatch : ∀ index, MeasurableSet (patch index))
    (hcover : K ⊆ ⋃ index, patch index)
    (derivative : Index → Real → (Real →L[Real] Real))
    (hderivative : ∀ index point, point ∈ patch index →
      HasFDerivWithinAt chart (derivative index point)
        (patch index) point)
    (hinjective : ∀ index, InjOn chart (patch index))
    (jacLower : Index → Real) (hjacLower : ∀ index, 0 < jacLower index)
    (hjac : ∀ index point, point ∈ patch index →
      jacLower index ≤ |(derivative index point).det|)
    (sourceDensity : Index → ENNReal)
    (hsource : ∀ index, source.restrict (patch index) ≤
      sourceDensity index •
        (volume : Measure Real).restrict (patch index))
    (delta : Real) :
    Measure.map chart source (Ioo (-delta) delta) ≤
      (∑ index, sourceDensity index *
        (ENNReal.ofReal (jacLower index))⁻¹) *
          ENNReal.ofReal (2 * delta) + source Kᶜ := by
  have hmain :=
    (scalarFinitePatchAtlas_map_restrict_and_full_apply_le
      source K hK chart hchart patch hpatch hcover derivative hderivative
      hinjective jacLower hjacLower hjac sourceDensity hsource).2
      (target := Ioo (-delta) delta) measurableSet_Ioo
  rw [Real.volume_Ioo] at hmain
  convert hmain using 1 <;> ring_nf

/-- A compact quantitative-good subset of one genuine actual mismatch fiber
admits a finite injectivity atlas.  `atlasCard` is the explicit fiber
multiplicity; `5/2` is the sharp mass density; `j₀` is the supplied compact
Jacobian lower bound. -/
theorem exists_atlasCard_physlibA1PairFiberCompact_smallBall
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed term)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, second)|) :
    ∃ atlasCard : Nat,
      (∀ {target : Set Real}, MeasurableSet target →
        Measure.map
            (fun second => physlibA1PairMismatchChart
              fixed site₁ site₂ observed term (first, second))
            (massCoordinateLaw.restrict K) target ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              (volume : Measure Real) target) ∧
      (∀ delta : Real,
        Measure.map
            (fun second => physlibA1PairMismatchChart
              fixed site₁ site₂ observed term (first, second))
            massCoordinateLaw (Ioo (-delta) delta) ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              ENNReal.ofReal (2 * delta) + massCoordinateLaw Kᶜ) := by
  classical
  let chart : Real → Real := fun second =>
    physlibA1PairMismatchChart
      fixed site₁ site₂ observed term (first, second)
  let derivative : Real → (Real →L[Real] Real) := fun second =>
    ContinuousLinearMap.toSpanSingleton Real
      (physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, second))
  have hchart : Measurable chart := by
    exact (measurable_physlibA1PairMismatchChart
      fixed site₁ site₂ observed term).comp
        (measurable_const.prodMk measurable_id)
  have hlocal : ∀ point : K, ∃ patch : Set Real,
      IsOpen patch ∧ point.1 ∈ patch ∧ InjOn chart patch := by
    intro point
    have hregular := hKregular point.1 point.2
    have hnonzero : physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, point.1) ≠ 0 := by
      exact abs_pos.mp (hj₀.trans_le (hjac point.1 point.2))
    obtain ⟨patch, hpoint, hopen, _hmeasurable, _hsupport, hinjective⟩ :=
      exists_physlibA1PairFiber_localInjectivePatch
        fixed hsite observed term hregular hnonzero
    exact ⟨patch, hopen, hpoint, hinjective⟩
  choose localPatch hopen hmem hinjective using hlocal
  obtain ⟨atlas, hcover⟩ := hK.elim_finite_subcover localPatch hopen (by
    intro point hpoint
    rw [mem_iUnion]
    exact ⟨⟨point, hpoint⟩, hmem ⟨point, hpoint⟩⟩)
  let AtlasIndex := {point : K // point ∈ atlas}
  let patch : AtlasIndex → Set Real := fun index =>
    K ∩ localPatch index.1
  have hpatch : ∀ index : AtlasIndex, MeasurableSet (patch index) := by
    intro index
    exact hK.isClosed.measurableSet.inter (hopen index.1).measurableSet
  have hcoverK : K ⊆ ⋃ index : AtlasIndex, patch index := by
    intro second hsecond
    rcases mem_iUnion₂.mp (hcover hsecond) with
      ⟨center, hcenter, hsecondPatch⟩
    rw [mem_iUnion]
    exact ⟨⟨center, hcenter⟩, hsecond, hsecondPatch⟩
  have hderivative : ∀ index : AtlasIndex, ∀ second ∈ patch index,
      HasFDerivWithinAt chart (derivative second) (patch index) second := by
    intro index second hsecond
    have hstrict := hasStrictDerivAt_physlibA1PairMismatchFiber
      fixed hsite observed term (hKregular second hsecond.1)
    exact hstrict.hasDerivAt.hasFDerivAt.hasFDerivWithinAt
  have hsource : ∀ index : AtlasIndex,
      massCoordinateLaw.restrict (patch index) ≤
        (5 / 2 : ENNReal) •
          (volume : Measure Real).restrict (patch index) := by
    intro index
    calc
      massCoordinateLaw.restrict (patch index) ≤
          ((5 / 2 : ENNReal) •
            (volume : Measure Real)).restrict (patch index) :=
        Measure.restrict_mono_measure
          massCoordinateLaw_le_fiveHalves_smul_volume _
      _ = (5 / 2 : ENNReal) •
          (volume : Measure Real).restrict (patch index) := by
        rw [Measure.restrict_smul]
  have hmain := scalarFinitePatchAtlas_map_restrict_and_full_apply_le
    massCoordinateLaw K hK.isClosed.measurableSet chart hchart patch hpatch
      hcoverK (fun _index => derivative)
      (fun index => hderivative index)
      (fun index => (hinjective index.1).mono inter_subset_right)
      (fun _index : AtlasIndex => j₀) (fun _ => hj₀)
      (fun _index second hsecond => by
        simpa [derivative] using hjac second hsecond.1)
      (fun _index : AtlasIndex => (5 / 2 : ENNReal)) hsource
  refine ⟨atlas.card, ?_, ?_⟩
  · intro target htarget
    simpa [AtlasIndex, chart] using hmain.1 htarget
  · intro delta
    have hfull := hmain.2 (target := Ioo (-delta) delta) measurableSet_Ioo
    rw [Real.volume_Ioo] at hfull
    convert hfull using 1 <;>
      simp [AtlasIndex, chart]
    rw [show delta + delta = delta * 2 by ring,
      ENNReal.ofReal_mul' (by norm_num : (0 : Real) ≤ 2)]
    norm_num [mul_assoc, mul_comm, mul_left_comm]

/-- The indices excluded from an ordinary-denominator finite set are retained
as a separate history sector. -/
def physlibFixedOrderRetainedSector
    {J : Type*} [Fintype J] [DecidableEq J]
    (ordinary : Finset J) : Finset J :=
  Finset.univ \ ordinary

theorem ordinary_union_physlibFixedOrderRetainedSector_eq_univ
    {J : Type*} [Fintype J] [DecidableEq J]
    (ordinary : Finset J) :
    ordinary ∪ physlibFixedOrderRetainedSector ordinary = Finset.univ := by
  ext j
  simp [physlibFixedOrderRetainedSector]

theorem ordinary_disjoint_physlibFixedOrderRetainedSector
    {J : Type*} [Fintype J] [DecidableEq J]
    (ordinary : Finset J) :
    Disjoint ordinary (physlibFixedOrderRetainedSector ordinary) := by
  exact Finset.disjoint_sdiff

/-- Union of the centered near events for a supplied finite type of ordinary
cumulative denominators. -/
def physlibFixedOrderOrdinaryNearEvent
    {Ordinary : Type*} [Fintype Ordinary]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Ordinary → QuadraticPhaseTerm N) (first delta : Real) : Set Real :=
  ⋃ j, (fun second => physlibA1PairMismatchChart
    fixed site₁ site₂ observed (term j) (first, second)) ⁻¹'
      Ioo (-delta) delta

/-- Union of the compact-atlas exceptional events for those same ordinary
denominators. -/
def physlibFixedOrderOrdinaryCompactBadEvent
    {Ordinary : Type*} [Fintype Ordinary]
    (K : Ordinary → Set Real) : Set Real :=
  ⋃ j, (K j)ᶜ

/-- Fixed-order quantitative small-ball bridge.  Each ordinary cumulative
denominator receives its own compact set, atlas multiplicity, and Jacobian
threshold.  The exceptional term is one probability of the union of compact
complements, not a false independence product. -/
theorem exists_atlasCard_physlibFixedOrderOrdinaryNearEvent_le
    {Ordinary : Type*} [Fintype Ordinary]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Ordinary → QuadraticPhaseTerm N) (first : Real)
    (K : Ordinary → Set Real) (hK : ∀ j, IsCompact (K j))
    (hKregular : ∀ j second, second ∈ K j →
      (first, second) ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed (term j))
    (j₀ : Ordinary → Real) (hj₀ : ∀ j, 0 < j₀ j)
    (hjac : ∀ j second, second ∈ K j → j₀ j ≤
      |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed (term j) (first, second)|) :
    ∃ atlasCard : Ordinary → Nat, ∀ delta : Real,
      massCoordinateLaw (physlibFixedOrderOrdinaryNearEvent
          fixed site₁ site₂ observed term first delta) ≤
        (∑ j, (atlasCard j : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal (j₀ j))⁻¹)) *
            ENNReal.ofReal (2 * delta) +
          massCoordinateLaw (physlibFixedOrderOrdinaryCompactBadEvent K) := by
  classical
  have hcompact : ∀ j, ∃ atlasCard : Nat,
      ∀ {target : Set Real}, MeasurableSet target →
        Measure.map
            (fun second => physlibA1PairMismatchChart
              fixed site₁ site₂ observed (term j) (first, second))
            (massCoordinateLaw.restrict (K j)) target ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal (j₀ j))⁻¹)) *
              (volume : Measure Real) target := by
    intro j
    obtain ⟨atlasCard, hregular, _hfull⟩ :=
      exists_atlasCard_physlibA1PairFiberCompact_smallBall
        fixed hsite observed (term j) first (K j) (hK j)
        (hKregular j) (hj₀ j) (hjac j)
    exact ⟨atlasCard, hregular⟩
  choose atlasCard hregular using hcompact
  refine ⟨atlasCard, ?_⟩
  intro delta
  let near : Ordinary → Set Real := fun j =>
    (fun second => physlibA1PairMismatchChart
      fixed site₁ site₂ observed (term j) (first, second)) ⁻¹'
        Ioo (-delta) delta
  let goodNear : Ordinary → Set Real := fun j => near j ∩ K j
  let bad := physlibFixedOrderOrdinaryCompactBadEvent K
  have hsubset : physlibFixedOrderOrdinaryNearEvent
      fixed site₁ site₂ observed term first delta ⊆
      bad ∪ ⋃ j, goodNear j := by
    intro second hsecond
    rcases mem_iUnion.mp hsecond with ⟨j, hj⟩
    by_cases hbad : second ∈ bad
    · exact Or.inl hbad
    · apply Or.inr
      rw [mem_iUnion]
      refine ⟨j, hj, ?_⟩
      by_contra hnotK
      exact hbad (mem_iUnion.mpr ⟨j, hnotK⟩)
  have hgoodBound : ∀ j,
      massCoordinateLaw (goodNear j) ≤
        ((atlasCard j : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal (j₀ j))⁻¹)) *
            ENNReal.ofReal (2 * delta) := by
    intro j
    have hchart : Measurable fun second => physlibA1PairMismatchChart
        fixed site₁ site₂ observed (term j) (first, second) :=
      (measurable_physlibA1PairMismatchChart
        fixed site₁ site₂ observed (term j)).comp
          (measurable_const.prodMk measurable_id)
    have heq : massCoordinateLaw (goodNear j) =
        Measure.map
          (fun second => physlibA1PairMismatchChart
            fixed site₁ site₂ observed (term j) (first, second))
          (massCoordinateLaw.restrict (K j)) (Ioo (-delta) delta) := by
      rw [Measure.map_apply hchart measurableSet_Ioo,
        Measure.restrict_apply (measurableSet_Ioo.preimage hchart)]
    rw [heq]
    have hbound := hregular j (target := Ioo (-delta) delta) measurableSet_Ioo
    rw [Real.volume_Ioo] at hbound
    convert hbound using 1 <;> ring_nf
  calc
    massCoordinateLaw (physlibFixedOrderOrdinaryNearEvent
        fixed site₁ site₂ observed term first delta) ≤
      massCoordinateLaw (bad ∪ ⋃ j, goodNear j) := measure_mono hsubset
    _ ≤ massCoordinateLaw bad +
        massCoordinateLaw (⋃ j, goodNear j) := measure_union_le _ _
    _ ≤ massCoordinateLaw bad +
        ∑' j, massCoordinateLaw (goodNear j) := by
      gcongr
      exact measure_iUnion_le _
    _ ≤ massCoordinateLaw bad +
        ∑ j, ((atlasCard j : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal (j₀ j))⁻¹)) *
            ENNReal.ofReal (2 * delta) := by
      simp only [tsum_fintype]
      gcongr with j
      exact hgoodBound j
    _ = (∑ j, (atlasCard j : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal (j₀ j))⁻¹)) *
            ENNReal.ofReal (2 * delta) + massCoordinateLaw bad := by
      rw [Finset.sum_mul]
      ac_rfl

end

end ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall
