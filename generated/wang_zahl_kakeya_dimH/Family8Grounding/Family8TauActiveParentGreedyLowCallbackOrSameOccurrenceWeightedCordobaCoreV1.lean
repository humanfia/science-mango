import Family8Grounding.Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaV1
import Family8Grounding.Family8TauActiveParentSameOccurrenceWeightedCordobaScalarEnvelopeV1
import Mathlib.Tactic

/-!
# Tau-active greedy split without parent-datum admissibility

The greedy first-low cut, the factor-two mass split, and the same-occurrence
weighted selection are finite combinatorics.  They do not require the
tau-parent family itself to be pairwise essentially distinct.

This file records that dependency boundary literally.  The low branch is
handed to a local callback with exactly its factor-two mass certificate and
Katz--Tao restriction.  The high branch retains the same greedy partition,
selected prefix, occurrence `q`, block, and zero-extended shading.  Its
occurrence certificate contains only the two facts used later: high density
and the constant-one Frostman property of the same block.

The quantitative John/Cordoba step still uses admissibility of the *fine*
datum, solely through its unit-ball support.  It never assumes admissibility
of the enlarged tau-parent datum.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.GreedyLateTailRestart
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyFirstLowDensityDichotomyV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaV1
open Family8TauActiveParentSameOccurrenceWeightedCordobaScalarEnvelopeV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The actual high-occurrence payload used by the same-block route.  The
discarded field from `ActualHighConcentrationOccurrence` is precisely
admissibility of the restricted tau-parent datum. -/
def CoreHighConcentrationOccurrence
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks D.family.bodyFamily P).length) : Prop :=
  A < blockDensity D.family.bodyFamily
      (blockAt D.family.bodyFamily P q) /\
    IsFrostmanIn 1
      (restrictActualTubeDatum D
        (blockAt D.family.bodyFamily P q).fiber).family.bodyFamily
      (blockAt D.family.bodyFamily P q).body

/-- High density alone gives the core occurrence certificate.  The greedy
block Frostman statement is purely combinatorial and does not use `D`'s
admissibility. -/
theorem coreHighConcentrationOccurrence_of_density_gt
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks D.family.bodyFamily P).length)
    (hhigh : A < blockDensity D.family.bodyFamily
      (blockAt D.family.bodyFamily P q)) :
    CoreHighConcentrationOccurrence D P A q := by
  refine ⟨hhigh, ?_⟩
  apply isFrostmanIn_restrictActualTubeDatum_of_isFrostmanOn
  exact blockAt_isFrostmanOn_one_of_subset
    D.family.bodyFamily Finset.univ P (fun _ hi => hi) q

/-- The honest first-low split with all tau-parent admissibility fields
removed.  Its low branch is the literal factor-two tail and its sharp local
Katz--Tao certificate.  Its high branch is the literal prefix and the same
actual greedy occurrences, with only the payload consumed downstream. -/
theorem exists_factorTwo_lowKatzTaoRestriction_or_coreHighOccurrencePrefix
    (D : ActualTubeDatum delta index) (A : ENNReal) :
    (exists selected : Finset index,
        D.shading.shadingMass <= 2 *
          (restrictActualTubeDatum D selected).shading.shadingMass /\
        IsKatzTao A
          (restrictActualTubeDatum D selected).family.bodyFamily) \/
      exists P : GreedyDensityPartition D.family.bodyFamily
          (hullCandidates (Finset.univ : Finset index))
          (hullContainer D.family.bodyFamily) Finset.univ,
        exists selected : Finset index,
          D.shading.shadingMass <= 2 *
            (restrictActualTubeDatum D selected).shading.shadingMass /\
          forall i, i ∈ selected ->
            exists q : Fin (blocks D.family.bodyFamily P).length,
              i ∈ (blockAt D.family.bodyFamily P q).fiber /\
              CoreHighConcentrationOccurrence D P A q := by
  classical
  obtain ⟨P, _hcover, _hlength, _hcross⟩ :=
    exists_fullConvexGreedyDensityPartition D.family.bodyFamily Finset.univ
  let low := lowDensityOccurrences D.family.bodyFamily Finset.univ P A
  by_cases hlow : low.Nonempty
  · let k0 : Fin (blocks D.family.bodyFamily P).length := low.min' hlow
    have hk0mem : k0 ∈ low := Finset.min'_mem low hlow
    have hk0low : blockDensity D.family.bodyFamily
        (blockAt D.family.bodyFamily P k0) <= A := by
      exact (mem_lowDensityOccurrences
        D.family.bodyFamily Finset.univ P A k0).mp hk0mem
    have hprior : forall q : Fin (blocks D.family.bodyFamily P).length,
        q < k0 -> A < blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) := by
      intro q hq
      by_contra hnot
      have hqLow : blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) <= A := le_of_not_gt hnot
      have hqmem : q ∈ low :=
        (mem_lowDensityOccurrences
          D.family.bodyFamily Finset.univ P A q).mpr hqLow
      exact (not_le_of_gt hq) (Finset.min'_le low q hqmem)
    rcases source_shadingMass_le_two_mul_tail_or_prefix D P k0 with
      htail | hprefix
    · left
      refine ⟨activeAt D.family.bodyFamily P k0, htail, ?_⟩
      apply isKatzTao_restrictActualTubeDatum_of_isKatzTaoOn
      exact activeAt_isKatzTaoOn_of_blockDensity_le
        D.family.bodyFamily Finset.univ P (fun _ hi => hi) k0 A hk0low
    · right
      refine ⟨P, Finset.univ \ activeAt D.family.bodyFamily P k0,
        hprefix, ?_⟩
      intro i hi
      obtain ⟨q, _hqk, hiq⟩ :=
        exists_prior_block_of_mem_sdiff_activeAt
          D.family.bodyFamily P k0 hi
      refine ⟨q, hiq, ?_⟩
      exact coreHighConcentrationOccurrence_of_density_gt
        D P A q (hprior q _hqk)
  · right
    have hallHigh : forall q : Fin (blocks D.family.bodyFamily P).length,
        A < blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) := by
      intro q
      have hnotLow : ¬ (blockDensity D.family.bodyFamily
          (blockAt D.family.bodyFamily P q) <= A) := by
        intro hqLow
        exact hlow ⟨q, (mem_lowDensityOccurrences
          D.family.bodyFamily Finset.univ P A q).mpr hqLow⟩
      exact lt_of_not_ge hnotLow
    have hmassEq : (restrictActualTubeDatum D
        (Finset.univ : Finset index)).shading.shadingMass =
        D.shading.shadingMass := by
      rw [restrictActualTubeDatum_shadingMass]
      unfold Shading.shadingMass
      simp
    have hmass : D.shading.shadingMass <= 2 *
        (restrictActualTubeDatum D
          (Finset.univ : Finset index)).shading.shadingMass := by
      rw [hmassEq]
      calc
        D.shading.shadingMass = 1 * D.shading.shadingMass := by simp
        _ <= 2 * D.shading.shadingMass := by
          exact mul_le_mul' (by norm_num : (1 : ENNReal) <= 2) le_rfl
    refine ⟨P, Finset.univ, hmass, ?_⟩
    intro i _hi
    let q := locate D.family.bodyFamily P (Finset.mem_univ i)
    exact ⟨q, mem_blockAt_locate D.family.bodyFamily P (Finset.mem_univ i),
      coreHighConcentrationOccurrence_of_density_gt
        D P A q (hallHigh q)⟩

/-- Choose one containing core-high occurrence for each selected index. -/
noncomputable def chosenCoreHighOccurrence
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (i : {i // i ∈ selected}) :
    Fin (blocks D.family.bodyFamily P).length :=
  Classical.choose (hcover i.1 i.2)

theorem chosenCoreHighOccurrence_mem_block
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (i : {i // i ∈ selected}) :
    i.1 ∈ (blockAt D.family.bodyFamily P
      (chosenCoreHighOccurrence D P A selected hcover i)).fiber := by
  exact (Classical.choose_spec (hcover i.1 i.2)).1

theorem chosenCoreHighOccurrence_is_core
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (i : {i // i ∈ selected}) :
    CoreHighConcentrationOccurrence D P A
      (chosenCoreHighOccurrence D P A selected hcover i) := by
  exact (Classical.choose_spec (hcover i.1 i.2)).2

/-- Only labels actually chosen by the selected prefix are charged. -/
noncomputable def occupiedCoreHighOccurrences
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q) :
    Finset (Fin (blocks D.family.bodyFamily P).length) := by
  classical
  exact (Finset.univ : Finset {i // i ∈ selected}).image
    (chosenCoreHighOccurrence D P A selected hcover)

theorem coreHighOccurrence_of_mem_occupied
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    {q : Fin (blocks D.family.bodyFamily P).length}
    (hq : q ∈ occupiedCoreHighOccurrences D P A selected hcover) :
    CoreHighConcentrationOccurrence D P A q := by
  classical
  rw [occupiedCoreHighOccurrences] at hq
  obtain ⟨i, _hi, hiq⟩ := Finset.mem_image.mp hq
  rw [← hiq]
  exact chosenCoreHighOccurrence_is_core D P A selected hcover i

/-- Selected indices assigned to one literal greedy occurrence, reindexed on
that same block. -/
noncomputable def sameCoreOccurrenceBlockBucket
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (q : Fin (blocks D.family.bodyFamily P).length) :
    Finset {i // i ∈ (blockAt D.family.bodyFamily P q).fiber} := by
  classical
  let source := (Finset.univ : Finset {i // i ∈ selected})
  let label := chosenCoreHighOccurrence D P A selected hcover
  let selectedFiber := dyadicFiber source label q
  exact selectedFiber.attach.image fun i =>
    ⟨i.1.1, by
      have hiLabel : label i.1 = q :=
        (mem_dyadicFiber source label q i.1).mp i.2 |>.2
      have hiBlock := chosenCoreHighOccurrence_mem_block
        D P A selected hcover i.1
      simpa only [label, hiLabel] using hiBlock⟩

/-- The same-q selected shading, zero outside the chosen bucket. -/
noncomputable def sameCoreOccurrenceBlockShading
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (q : Fin (blocks D.family.bodyFamily P).length) :
    Shading (selectedCoarseFamily D.family.bodyFamily
      (blockAt D.family.bodyFamily P q).fiber) :=
  (IndexedShadingRefinement.restrictTo
    (selectedCoarseShading D.shading
      (blockAt D.family.bodyFamily P q).fiber)
    (sameCoreOccurrenceBlockBucket D P A selected hcover q)).shading

theorem sameCoreOccurrenceBlockShading_mass_eq
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (q : Fin (blocks D.family.bodyFamily P).length) :
    (sameCoreOccurrenceBlockShading D P A selected hcover q).shadingMass =
      ∑ i ∈ dyadicFiber
          (Finset.univ : Finset {i // i ∈ selected})
          (chosenCoreHighOccurrence D P A selected hcover) q,
        volume (D.shading.carrier i.1) := by
  classical
  rw [sameCoreOccurrenceBlockShading, shadingMass_restrictTo_eq_sum]
  simp only [selectedCoarseShading_carrier]
  rw [sameCoreOccurrenceBlockBucket]
  rw [Finset.sum_image]
  · simpa only using
      (Finset.sum_attach
        (dyadicFiber
          (Finset.univ : Finset {i // i ∈ selected})
          (chosenCoreHighOccurrence D P A selected hcover) q)
        (fun i => volume (D.shading.carrier i.1)))
  · intro a _ha b _hb hab
    have habVal : a.1.1 = b.1.1 := congrArg (fun z => z.1) hab
    exact Subtype.ext (Subtype.ext habVal)

theorem sameCoreOccurrenceBlockShading_shadedUnion_subset
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (q : Fin (blocks D.family.bodyFamily P).length) :
    (sameCoreOccurrenceBlockShading D P A selected hcover q).shadedUnion ⊆
      D.shading.shadedUnion := by
  let blockShading := selectedCoarseShading D.shading
    (blockAt D.family.bodyFamily P q).fiber
  have hrestricted :
      (sameCoreOccurrenceBlockShading D P A selected hcover q).shadedUnion ⊆
        blockShading.shadedUnion := by
    exact (IndexedShadingRefinement.restrictTo blockShading
      (sameCoreOccurrenceBlockBucket D P A selected hcover q)).shadedUnion_subset
  intro x hx
  have hxBlock := hrestricted hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxBlock
  exact Set.mem_iUnion.mpr ⟨i.1, hxi⟩

/-- Same-q weighted pigeonholing for core occurrences.  It retains the exact
occupied-label loss and returns the high/Frostman certificate for that very
same `q`. -/
theorem exists_sameCoreOccurrenceBlockShading_weighted_retention_of_source_ne_zero
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q)
    (firstLoss : ENNReal)
    (hfirst : D.shading.shadingMass <= firstLoss *
      (restrictActualTubeDatum D selected).shading.shadingMass)
    (hsource : D.shading.shadingMass ≠ 0) :
    exists q : Fin (blocks D.family.bodyFamily P).length,
      q ∈ occupiedCoreHighOccurrences D P A selected hcover /\
      CoreHighConcentrationOccurrence D P A q /\
      (restrictActualTubeDatum D selected).shading.shadingMass <=
          ((occupiedCoreHighOccurrences
            D P A selected hcover).card : ENNReal) *
            (sameCoreOccurrenceBlockShading
              D P A selected hcover q).shadingMass /\
      D.shading.shadingMass <=
          (firstLoss *
            ((occupiedCoreHighOccurrences
              D P A selected hcover).card : ENNReal)) *
            (sameCoreOccurrenceBlockShading
              D P A selected hcover q).shadingMass /\
      D.shading.averageMultiplicity <=
          (firstLoss *
            ((occupiedCoreHighOccurrences
              D P A selected hcover).card : ENNReal)) *
            (sameCoreOccurrenceBlockShading
              D P A selected hcover q).averageMultiplicity := by
  classical
  have hselected : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero :
        (restrictActualTubeDatum D selected).shading.shadingMass = 0 := by
      rw [restrictActualTubeDatum_shadingMass, hselectedEmpty]
      simp
    rw [hzero, mul_zero] at hfirst
    exact hsource (bot_unique hfirst)
  let source := (Finset.univ : Finset {i // i ∈ selected})
  let label := chosenCoreHighOccurrence D P A selected hcover
  let labels := occupiedCoreHighOccurrences D P A selected hcover
  let weight : {i // i ∈ selected} -> ENNReal := fun i =>
    volume (D.shading.carrier i.1)
  let fiberWeight : Fin (blocks D.family.bodyFamily P).length -> ENNReal :=
    fun q => ∑ i ∈ dyadicFiber source label q, weight i
  have hlabels : labels.Nonempty := by
    let i0 : {i // i ∈ selected} :=
      ⟨hselected.choose, hselected.choose_spec⟩
    refine ⟨label i0, ?_⟩
    exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩
  obtain ⟨q, hq, hmax⟩ :=
    Finset.exists_max_image labels fiberWeight hlabels
  have hmaps : ∀ i ∈ source, label i ∈ labels := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hpartition :
      (∑ i ∈ source, weight i) =
        ∑ q' ∈ labels, fiberWeight q' := by
    change (∑ i ∈ source, weight i) =
      ∑ q' ∈ labels, ∑ i ∈ source with label i = q', weight i
    exact (Finset.sum_fiberwise_of_maps_to
      (s := source) (t := labels) (g := label) hmaps weight).symm
  have hweighted :
      (∑ i ∈ source, weight i) <= labels.card • fiberWeight q := by
    calc
      (∑ i ∈ source, weight i) =
          ∑ q' ∈ labels, fiberWeight q' := hpartition
      _ <= labels.card • fiberWeight q :=
        Finset.sum_le_card_nsmul labels fiberWeight (fiberWeight q)
          (fun q' hq' => hmax q' hq')
  have hselectedMass :
      (restrictActualTubeDatum D selected).shading.shadingMass =
        ∑ i ∈ (Finset.univ : Finset {i // i ∈ selected}),
          volume (D.shading.carrier i.1) := by
    rw [restrictActualTubeDatum_shadingMass]
    exact (Finset.sum_attach selected
      (fun i => volume (D.shading.carrier i))).symm
  have hbucketMass := sameCoreOccurrenceBlockShading_mass_eq
    D P A selected hcover q
  have hretained :
      (restrictActualTubeDatum D selected).shading.shadingMass <=
        ((occupiedCoreHighOccurrences
          D P A selected hcover).card : ENNReal) *
          (sameCoreOccurrenceBlockShading
            D P A selected hcover q).shadingMass := by
    rw [hselectedMass, hbucketMass]
    simpa only [source, weight, fiberWeight, labels, label,
      nsmul_eq_mul] using hweighted
  have hsourceMass : D.shading.shadingMass <=
      (firstLoss *
        ((occupiedCoreHighOccurrences
          D P A selected hcover).card : ENNReal)) *
        (sameCoreOccurrenceBlockShading
          D P A selected hcover q).shadingMass := by
    calc
      D.shading.shadingMass <= firstLoss *
          (restrictActualTubeDatum D selected).shading.shadingMass := hfirst
      _ <= firstLoss *
          (((occupiedCoreHighOccurrences
            D P A selected hcover).card : ENNReal) *
            (sameCoreOccurrenceBlockShading
              D P A selected hcover q).shadingMass) :=
        mul_le_mul' le_rfl hretained
      _ = (firstLoss *
          ((occupiedCoreHighOccurrences
            D P A selected hcover).card : ENNReal)) *
            (sameCoreOccurrenceBlockShading
              D P A selected hcover q).shadingMass := by
        ac_rfl
  let Z := sameCoreOccurrenceBlockShading D P A selected hcover q
  have hunion : Z.shadedUnion ⊆ D.shading.shadedUnion :=
    sameCoreOccurrenceBlockShading_shadedUnion_subset
      D P A selected hcover q
  have hsourceAverage : D.shading.averageMultiplicity <=
      (firstLoss *
        ((occupiedCoreHighOccurrences
          D P A selected hcover).card : ENNReal)) *
        Z.averageMultiplicity := by
    unfold Shading.averageMultiplicity
    calc
      D.shading.shadingMass / volume D.shading.shadedUnion <=
          ((firstLoss *
            ((occupiedCoreHighOccurrences
              D P A selected hcover).card : ENNReal)) *
              Z.shadingMass) / volume D.shading.shadedUnion :=
        ENNReal.div_le_div_right hsourceMass _
      _ <= ((firstLoss *
            ((occupiedCoreHighOccurrences
              D P A selected hcover).card : ENNReal)) *
              Z.shadingMass) / volume Z.shadedUnion :=
        ENNReal.div_le_div_left (measure_mono hunion) _
      _ = (firstLoss *
            ((occupiedCoreHighOccurrences
              D P A selected hcover).card : ENNReal)) *
              (Z.shadingMass / volume Z.shadedUnion) := by
        simp only [div_eq_mul_inv]
        ac_rfl
  exact ⟨q, hq,
    coreHighOccurrence_of_mem_occupied D P A selected hcover hq,
    hretained, hsourceMass, hsourceAverage⟩

/-- Fine-datum support supplies the logarithmic side bucket while retaining
both the affine mass payment and the quantitative Cordoba average bound.
This is the support-correct replacement for the older tau-parent-B1 helper. -/
theorem exists_selectedParentArbitraryPlankBucket_massRetention_and_averageMultiplicity_le_of_fine_admissible
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) /\
      0 < bucketShortA label /\
      bucketShortA label <= bucketShortB label /\
      bucketShortB label <= 1 /\
      exists hplank : forall p,
          p ∈ sideShapeBucket Finset.univ side label ->
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (selectedParentAffineFamily
                (bucketNormalizedAffineEquiv e label) S B p),
        let Ybucket := selectedParentArbitraryPlankBucketShading
          e S B hrho label Z
        let hplankPos : forall q,
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
          selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
        let cert := chosenPlankCertificate hplankPos
        affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              Ybucket.shadingMass /\
          Z.averageMultiplicity <=
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              (2 * certifiedPlankDyadicFactor
                (certifiedPlankThresholdedLevels cert) KT
                  (certifiedPlankThresholdedAngleScaleCap 576 *
                    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                      quantitativeCarrierFloor Ybucket))) := by
  dsimp only
  have hbucket :=
    exists_selectedParentArbitraryPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr Z
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  refine ⟨label, hoccupied, ha, hab, hb, hplank, hretained, ?_⟩
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  have hsourceToBucket : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        Ybucket.averageMultiplicity :=
    arbitraryBlockShading_averageMultiplicity_le_bucketLoss_mul
      e S B hrho label Z
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) hretained
  have hcordoba :=
    selectedParentArbitraryPlankBucket_averageMultiplicity_le_quantitativePopularityJohn
      S hrho P k r hr label Z hplank KT hKT
  dsimp only at hcordoba
  exact hsourceToBucket.trans (mul_le_mul' le_rfl hcordoba)

variable {depth N : Nat} {epsilonLong : Real} {etaLong : Nat -> Real}

/-- Tau-active low-callback/high-Cordoba split with no admissibility premise
on the tau-parent datum.  The callback sees the exact low restriction.  In
the high branch the same `P`, selected prefix, `q`, block, and shading flow
through weighted retention and Cordoba. -/
theorem exists_tauActiveParent_lowCallback_or_sameCoreOccurrenceWeightedCordoba
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness
      D.family C N epsilonLong etaLong S)
    (A : ENNReal)
    (htauHalf : S.tau W.m <= (2 : NNReal)⁻¹)
    (lowResult : Prop)
    (closeLow : forall selected : Finset
        {k // k ∈ (tauScaleCover D C S W).activeCoarse},
      (activeParentActualTubeDatum
          (tauScaleCover D C S W) D.shading).shading.shadingMass <=
        2 * (restrictActualTubeDatum
          (activeParentActualTubeDatum
            (tauScaleCover D C S W) D.shading)
          selected).shading.shadingMass ->
      IsKatzTao A
        (restrictActualTubeDatum
          (activeParentActualTubeDatum
            (tauScaleCover D C S W) D.shading)
          selected).family.bodyFamily ->
      lowResult)
    (hsourceMass :
      (activeParentActualTubeDatum
        (tauScaleCover D C S W) D.shading).shading.shadingMass ≠ 0)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover D C S W).activeCoarseFamily) :
    lowResult \/
      exists P : GreedyDensityPartition
          (activeParentActualTubeDatum
            (tauScaleCover D C S W) D.shading).family.bodyFamily
          (hullCandidates (Finset.univ : Finset
            {k // k ∈ (tauScaleCover D C S W).activeCoarse}))
          (hullContainer
            (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading).family.bodyFamily)
          Finset.univ,
        exists selected : Finset
            {k // k ∈ (tauScaleCover D C S W).activeCoarse},
          exists hcover : (forall k, k ∈ selected ->
            exists q : Fin (blocks
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading).family.bodyFamily P).length,
              k ∈ (blockAt
                (activeParentActualTubeDatum
                  (tauScaleCover D C S W) D.shading).family.bodyFamily
                P q).fiber /\
              CoreHighConcentrationOccurrence
                (activeParentActualTubeDatum
                  (tauScaleCover D C S W) D.shading)
                P A q),
          exists q : Fin (blocks
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading).family.bodyFamily P).length,
            q ∈ occupiedCoreHighOccurrences
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading)
              P A selected hcover /\
            CoreHighConcentrationOccurrence
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading)
              P A q /\
            let B := (blockAt
              (tauScaleCover D C S W).activeCoarseFamily P q).fiber
            let e := contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover D C S W)
                (hD.delta_pos.trans_le (S.delta_le_tau W.m)) P q) r hr
            let parent := {p // p ∈ B}
            let side : parent -> Fin 3 -> NNReal := fun p =>
              selectedParentLongRelabeledSide e
                (tauScaleCover D C S W) B
                (hD.delta_pos.trans_le (S.delta_le_tau W.m)) p
            let Z := sameCoreOccurrenceBlockShading
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading)
              P A selected hcover q
            (restrictActualTubeDatum
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading)
              selected).shading.shadingMass <=
                ((occupiedCoreHighOccurrences
                  (activeParentActualTubeDatum
                    (tauScaleCover D C S W) D.shading)
                  P A selected hcover).card : ENNReal) * Z.shadingMass /\
            (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading).shading.shadingMass <=
                (2 * ((occupiedCoreHighOccurrences
                  (activeParentActualTubeDatum
                    (tauScaleCover D C S W) D.shading)
                  P A selected hcover).card : ENNReal)) * Z.shadingMass /\
            exists label : Fin 3 -> Int,
              label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
                (fun p => sideShapeLabel (side p)) /\
              0 < bucketShortA label /\
              bucketShortA label <= bucketShortB label /\
              bucketShortB label <= 1 /\
              exists hplank : forall p,
                  p ∈ sideShapeBucket Finset.univ side label ->
                    IsPlank 576 (bucketShortA label) (bucketShortB label)
                      (selectedParentAffineFamily
                        (bucketNormalizedAffineEquiv e label)
                        (tauScaleCover D C S W) B p),
                let Ybucket := selectedParentArbitraryPlankBucketShading
                  e (tauScaleCover D C S W) B
                  (hD.delta_pos.trans_le (S.delta_le_tau W.m))
                  label Z
                let hplankPos : forall t,
                    IsPlank 576 (bucketShortA label) (bucketShortB label)
                      (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
                  selectedParentPlankBucket_isPlank
                    e (tauScaleCover D C S W) B
                    (hD.delta_pos.trans_le (S.delta_le_tau W.m))
                    label hplank t.1
                let cert := chosenPlankCertificate hplankPos
                affineJacobian (bucketNormalizedAffineEquiv e label) *
                    Z.shadingMass <=
                  (selectedParentLogarithmicSideBucketLoss
                    (S.tau W.m) : ENNReal) * Ybucket.shadingMass /\
                Ybucket.shadingMass ≠ 0 /\
                (activeParentActualTubeDatum
                    (tauScaleCover D C S W) D.shading).shading.averageMultiplicity <=
                  (2 *
                    ((occupiedCoreHighOccurrences
                      (activeParentActualTubeDatum
                        (tauScaleCover D C S W) D.shading)
                      P A selected hcover).card : ENNReal)) *
                    ((selectedParentLogarithmicSideBucketLoss
                        (S.tau W.m) : ENNReal) *
                      (2 * certifiedPlankDyadicFactor
                        (certifiedPlankThresholdedLevels cert) KT
                          (certifiedPlankThresholdedAngleScaleCap 576 *
                            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                                ENNReal) ^ 3) /
                              quantitativeCarrierFloor Ybucket)))) := by
  let parentD := activeParentActualTubeDatum
    (tauScaleCover D C S W) D.shading
  have hsplit :=
    exists_factorTwo_lowKatzTaoRestriction_or_coreHighOccurrencePrefix
      parentD A
  rcases hsplit with hlow | hhigh
  · left
    obtain ⟨selected, hmass, hlocalKT⟩ := hlow
    exact closeLow selected hmass hlocalKT
  · right
    obtain ⟨P, selected, hmass, hcover⟩ := hhigh
    have hselection :=
      exists_sameCoreOccurrenceBlockShading_weighted_retention_of_source_ne_zero
        parentD P A selected hcover 2 hmass hsourceMass
    obtain ⟨q, hq, hqcore, hselectedMass, hsourceSelectedMass,
      hsourceAverage⟩ := hselection
    let Z := sameCoreOccurrenceBlockShading parentD P A selected hcover q
    have hrho : 0 < S.tau W.m :=
      hD.delta_pos.trans_le (S.delta_le_tau W.m)
    have hrhoOne : S.tau W.m <= 1 :=
      htauHalf.trans (by norm_num)
    have hcordoba :=
      exists_selectedParentArbitraryPlankBucket_massRetention_and_averageMultiplicity_le_of_fine_admissible
        D hD (tauScaleCover D C S W) hrho hrhoOne
        P q r hr Z KT hKT
    dsimp only at hcordoba
    obtain ⟨label, hoccupied, ha, hab, hb, hplank, hretained,
      hbound⟩ := hcordoba
    have hZMassNe : Z.shadingMass ≠ 0 := by
      intro hzero
      have hle := hsourceSelectedMass
      rw [hzero, mul_zero] at hle
      exact hsourceMass (bot_unique hle)
    have hYbucketMassNe :=
      bucket_ne_zero_of_nonzero_source_and_retention
        (affineJacobian_pos
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover D C S W) hrho P q) r hr) label)).ne'
        hZMassNe hretained
    refine ⟨P, selected, hcover, q, hq, hqcore,
      hselectedMass, hsourceSelectedMass,
      label, hoccupied, ha, hab, hb, hplank, hretained,
      hYbucketMassNe, ?_⟩
    exact hsourceAverage.trans (mul_le_mul' le_rfl hbound)

#print axioms CoreHighConcentrationOccurrence
#print axioms coreHighConcentrationOccurrence_of_density_gt
#print axioms
  exists_factorTwo_lowKatzTaoRestriction_or_coreHighOccurrencePrefix
#print axioms occupiedCoreHighOccurrences
#print axioms sameCoreOccurrenceBlockShading
#print axioms
  exists_sameCoreOccurrenceBlockShading_weighted_retention_of_source_ne_zero
#print axioms
  exists_selectedParentArbitraryPlankBucket_massRetention_and_averageMultiplicity_le_of_fine_admissible
#print axioms
  exists_tauActiveParent_lowCallback_or_sameCoreOccurrenceWeightedCordoba

end
end Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
