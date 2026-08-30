import ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall
import ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberLocalLinearSmallBall

/-!
# Compact actual iterated-A2 pair-fiber atlases

The actual iterated-`A2` mismatch fiber is only locally invertible away from
the critical spectral set.  This module replaces the false global-fiber
injectivity premise by a finite atlas on an explicitly supplied compact set
`K`.  The assumptions are fully quantitative: `K` lies in the genuine
simple-positive spectral source and the actual vertical Jacobian is bounded
below by `j₀ > 0` on `K`.

Compactness selects finitely many local inverse-function patches.  On the
regular part the pushed-forward one-mass law is dominated by

`atlasCard * (5/2) * j₀⁻¹ • volume`.

The full centered small ball adds exactly `massCoordinateLaw Kᶜ`.  A finite
ordinary-channel theorem sums these atlas costs without using independence
between exceptional events.

Charge-matched total channels are not hidden in the atlas.  Their mismatch
and vertical Jacobian vanish identically, so a positive-Jacobian ordinary
sector with nonempty compact sets automatically places them in the retained
sector.  No bad-set mass estimate, volume-uniform atlas bound, RPA closure,
Markov approximation, or recollision estimate is asserted here.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberLocalLinearSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A compact quantitative-good subset of one actual iterated-`A2` mismatch
fiber admits a finite injectivity atlas.  The first conclusion is a measure
domination statement on the restricted law.  The second conclusion restores
the complete one-mass law and keeps exactly the mass of `Kᶜ` as an explicit
exceptional term. -/
theorem exists_atlasCard_physlibIteratedA2PairFiberCompact_smallBall
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ channel observed term)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second)|) :
    ∃ atlasCard : Nat,
      Measure.map
          (fun second => physlibIteratedA2PairMismatchChart
            fixed site₁ site₂ channel observed term (first, second))
          (massCoordinateLaw.restrict K) ≤
        ((atlasCard : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) •
            (volume : Measure Real) ∧
      ∀ delta : Real,
        Measure.map
            (fun second => physlibIteratedA2PairMismatchChart
              fixed site₁ site₂ channel observed term (first, second))
            massCoordinateLaw (Ioo (-delta) delta) ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              ENNReal.ofReal (2 * delta) + massCoordinateLaw Kᶜ := by
  classical
  let chart : Real → Real := fun second =>
    physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term (first, second)
  let derivative : Real → (Real →L[Real] Real) := fun second =>
    ContinuousLinearMap.toSpanSingleton Real
      (physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second))
  have hchart : Measurable chart := by
    exact (measurable_physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ channel observed term).comp
        (measurable_const.prodMk measurable_id)
  have hlocal : ∀ point : K, ∃ patch : Set Real,
      IsOpen patch ∧ point.1 ∈ patch ∧ InjOn chart patch := by
    intro point
    have hregular := hKregular point.1 point.2
    have hnonzero : physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, point.1) ≠ 0 := by
      exact abs_pos.mp (hj₀.trans_le (hjac point.1 point.2))
    obtain ⟨patch, hopen, _hmeasurable, hpoint, _hsupport, hanti,
        _hsmallBall⟩ :=
      exists_physlibIteratedA2PairFiber_localLinearSmallBall
        fixed hsite channel observed term hregular hnonzero
    refine ⟨patch, hopen, hpoint, ?_⟩
    intro firstPoint hfirstPoint secondPoint hsecondPoint heq
    have hsubtype : (⟨firstPoint, hfirstPoint⟩ : patch) =
        ⟨secondPoint, hsecondPoint⟩ := by
      apply hanti.injective
      simpa [Set.domRestrict, physlibIteratedA2PairMismatchFiber, chart]
        using heq
    exact congrArg Subtype.val hsubtype
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
    have hstrict := hasStrictDerivAt_physlibIteratedA2PairMismatchFiber
      fixed hsite channel observed term (hKregular second hsecond.1)
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
  · rw [Measure.le_iff]
    intro target htarget
    simpa [Measure.smul_apply, smul_eq_mul, AtlasIndex, chart] using
      hmain.1 htarget
  · intro delta
    have hfull := hmain.2 (target := Ioo (-delta) delta) measurableSet_Ioo
    rw [Real.volume_Ioo] at hfull
    convert hfull using 1 <;>
      simp [AtlasIndex, chart]
    rw [show delta + delta = delta * 2 by ring,
      ENNReal.ofReal_mul' (by norm_num : (0 : Real) ≤ 2)]
    norm_num [mul_assoc, mul_comm, mul_left_comm]

/-- A supplied finite type of ordinary iterated-`A2` channels has a centered
near-resonance event obtained by taking the union of its scalar channels. -/
def physlibIteratedA2FixedOrderOrdinaryNearEvent
    {Ordinary : Type*} [Fintype Ordinary]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (channel : Ordinary → IteratedA2MismatchChannel)
    (term : Ordinary → IteratedQuadraticSecondPicardCharacterTerm N)
    (first delta : Real) : Set Real :=
  ⋃ j, (fun second => physlibIteratedA2PairMismatchChart
    fixed site₁ site₂ (channel j) observed (term j) (first, second)) ⁻¹'
      Ioo (-delta) delta

/-- The single exceptional event retained when the finite ordinary-channel
atlas is glued.  It is a union, not an independence product. -/
def physlibIteratedA2FixedOrderOrdinaryCompactBadEvent
    {Ordinary : Type*} [Fintype Ordinary]
    (K : Ordinary → Set Real) : Set Real :=
  ⋃ j, (K j)ᶜ

/-- Fixed-order ordinary-channel compact-atlas bound.  Every channel keeps
its own compact set, atlas multiplicity, and positive Jacobian threshold.
All compact-complement errors are charged once through their union. -/
theorem exists_atlasCard_physlibIteratedA2FixedOrderOrdinaryNearEvent_le
    {Ordinary : Type*} [Fintype Ordinary]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (channel : Ordinary → IteratedA2MismatchChannel)
    (term : Ordinary → IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (K : Ordinary → Set Real)
    (hK : ∀ j, IsCompact (K j))
    (hKregular : ∀ j second, second ∈ K j →
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ (channel j) observed (term j))
    (j₀ : Ordinary → Real) (hj₀ : ∀ j, 0 < j₀ j)
    (hjac : ∀ j second, second ∈ K j → j₀ j ≤
      |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ (channel j) observed (term j)
          (first, second)|) :
    ∃ atlasCard : Ordinary → Nat, ∀ delta : Real,
      massCoordinateLaw
          (physlibIteratedA2FixedOrderOrdinaryNearEvent
            fixed site₁ site₂ observed channel term first delta) ≤
        (∑ j, (atlasCard j : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal (j₀ j))⁻¹)) *
            ENNReal.ofReal (2 * delta) +
          massCoordinateLaw
            (physlibIteratedA2FixedOrderOrdinaryCompactBadEvent K) := by
  classical
  have hcompact : ∀ j, ∃ atlasCard : Nat,
      Measure.map
          (fun second => physlibIteratedA2PairMismatchChart
            fixed site₁ site₂ (channel j) observed (term j) (first, second))
          (massCoordinateLaw.restrict (K j)) ≤
        ((atlasCard : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal (j₀ j))⁻¹)) •
            (volume : Measure Real) := by
    intro j
    obtain ⟨atlasCard, hregular, _hfull⟩ :=
      exists_atlasCard_physlibIteratedA2PairFiberCompact_smallBall
        fixed hsite (channel j) observed (term j) first (K j) (hK j)
        (hKregular j) (hj₀ j) (hjac j)
    exact ⟨atlasCard, hregular⟩
  choose atlasCard hregular using hcompact
  refine ⟨atlasCard, ?_⟩
  intro delta
  let near : Ordinary → Set Real := fun j =>
    (fun second => physlibIteratedA2PairMismatchChart
      fixed site₁ site₂ (channel j) observed (term j) (first, second)) ⁻¹'
        Ioo (-delta) delta
  let goodNear : Ordinary → Set Real := fun j => near j ∩ K j
  let bad := physlibIteratedA2FixedOrderOrdinaryCompactBadEvent K
  have hsubset : physlibIteratedA2FixedOrderOrdinaryNearEvent
      fixed site₁ site₂ observed channel term first delta ⊆
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
    have hchart : Measurable fun second =>
        physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ (channel j) observed (term j) (first, second) :=
      (measurable_physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ (channel j) observed (term j)).comp
          (measurable_const.prodMk measurable_id)
    have heq : massCoordinateLaw (goodNear j) =
        Measure.map
          (fun second => physlibIteratedA2PairMismatchChart
            fixed site₁ site₂ (channel j) observed (term j) (first, second))
          (massCoordinateLaw.restrict (K j)) (Ioo (-delta) delta) := by
      rw [Measure.map_apply hchart measurableSet_Ioo,
        Measure.restrict_apply (measurableSet_Ioo.preimage hchart)]
    rw [heq]
    have hbound := (Measure.le_iff.mp (hregular j))
      (Ioo (-delta) delta) measurableSet_Ioo
    rw [Measure.smul_apply, Real.volume_Ioo] at hbound
    convert hbound using 1 <;> ring_nf
  calc
    massCoordinateLaw (physlibIteratedA2FixedOrderOrdinaryNearEvent
        fixed site₁ site₂ observed channel term first delta) ≤
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

/-- Indices outside a chosen finite ordinary sector are retained for a
separate resonant/feedback/recollision analysis. -/
def physlibIteratedA2FixedOrderRetainedSector
    {J : Type*} [Fintype J] [DecidableEq J]
    (ordinary : Finset J) : Finset J :=
  Finset.univ \ ordinary

theorem ordinary_union_physlibIteratedA2FixedOrderRetainedSector_eq_univ
    {J : Type*} [Fintype J] [DecidableEq J]
    (ordinary : Finset J) :
    ordinary ∪ physlibIteratedA2FixedOrderRetainedSector ordinary =
      Finset.univ := by
  ext j
  simp [physlibIteratedA2FixedOrderRetainedSector]

theorem ordinary_disjoint_physlibIteratedA2FixedOrderRetainedSector
    {J : Type*} [Fintype J] [DecidableEq J]
    (ordinary : Finset J) :
    Disjoint ordinary
      (physlibIteratedA2FixedOrderRetainedSector ordinary) := by
  exact Finset.disjoint_sdiff

/-- A charge-matched total channel cannot belong to a nonempty ordinary
sector carrying the positive actual-Jacobian hypotheses used by the compact
atlas.  Thus it lies in the retained sector automatically; this is the exact
finite-order form of the resonant obstruction. -/
theorem chargeMatchedTotal_mem_physlibIteratedA2FixedOrderRetainedSector
    {J : Type*} [Fintype J] [DecidableEq J]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N) (first : Real)
    (ordinary : Finset J)
    (channel : J → IteratedA2MismatchChannel)
    (term : J → IteratedQuadraticSecondPicardCharacterTerm N)
    (K : J → Set Real) (hKnonempty : ∀ j ∈ ordinary, (K j).Nonempty)
    (j₀ : J → Real) (hj₀ : ∀ j ∈ ordinary, 0 < j₀ j)
    (hjac : ∀ j ∈ ordinary, ∀ second ∈ K j, j₀ j ≤
      |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ (channel j) observed (term j) (first, second)|)
    {j : J} (hchannel : channel j = .total)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge (term j)) :
    j ∈ physlibIteratedA2FixedOrderRetainedSector ordinary := by
  classical
  rw [physlibIteratedA2FixedOrderRetainedSector, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ j, ?_⟩
  intro hjordinary
  obtain ⟨second, hsecond⟩ := hKnonempty j hjordinary
  have hpositive := hj₀ j hjordinary
  have hlower := hjac j hjordinary second hsecond
  have hzero :=
    physlibIteratedA2TotalPairMismatchVerticalJacobian_eq_zero_of_chargeMatched
      fixed site₁ site₂ observed (term j) hcharge (first, second)
  rw [hchannel, hzero, abs_zero] at hlower
  exact (not_lt_of_ge hlower) hpositive

end

end ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall
