import Family8Grounding.Family8SelectedParentCordobaCoreGeometryV1
import Family8Grounding.Family8SelectedParentMassPopularFineLevelBucketV2
import Mathlib.Tactic

/-!
# Division-free Córdoba core for the mass-popular selected parent, V2

The selected-parent Córdoba core contains the genuine quotient
`containerVolume / (bucketMass / (2 * bucketCard))`.  The mass-popular bucket
theorem gives an inequality from the source active mass into `bucketMass`.
This module cancels those two literal occurrences of `bucketMass`, with all
zero and infinity side conditions proved from the actual selected bucket.

The output is a division-free core estimate.  Thus the remaining comparison
with Equation (46) no longer contains a popularity denominator or a selected
fibre mass callback; it is a scale/cardinality/source-mass estimate.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentMassPopularCordobaCoreV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCordobaCoreGeometryV1
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentLogarithmicCordobaCoreV2
open Family8SelectedParentMassPopularFineLevelBucketV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Division-free cancellation behind the mass-popular Córdoba core. -/
theorem massRetention_mul_cordobaQuotient_le
    {source bucket count loss KT containerVolume : ENNReal}
    (hretained : source ≤ loss * bucket)
    (hbucket0 : bucket ≠ 0) (hbucketTop : bucket ≠ ∞)
    (hcount0 : count ≠ 0) (hcountTop : count ≠ ∞) :
    source * (KT * (containerVolume / (bucket / count))) ≤
      loss * count * (KT * containerVolume) := by
  have hmean0 : bucket / count ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hbucket0, hcountTop⟩
  have hmeanTop : bucket / count ≠ ∞ :=
    ENNReal.div_ne_top hbucketTop hcount0
  have hcancel :
      bucket * (containerVolume / (bucket / count)) =
        count * containerVolume := by
    calc
      bucket * (containerVolume / (bucket / count)) =
          ((bucket / count) * count) *
            (containerVolume / (bucket / count)) := by
        rw [ENNReal.div_mul_cancel hcount0 hcountTop]
      _ = count *
          ((containerVolume / (bucket / count)) * (bucket / count)) := by
        ac_rfl
      _ = count * containerVolume := by
        rw [ENNReal.div_mul_cancel hmean0 hmeanTop]
  calc
    source * (KT * (containerVolume / (bucket / count))) ≤
        (loss * bucket) *
          (KT * (containerVolume / (bucket / count))) :=
      mul_le_mul' hretained le_rfl
    _ = loss * KT *
        (bucket * (containerVolume / (bucket / count))) := by
      ac_rfl
    _ = loss * KT * (count * containerVolume) := by rw [hcancel]
    _ = loss * count * (KT * containerVolume) := by ac_rfl

/-- The literal division-free budget after selecting the mass-popular greedy
block and its actual side bucket. -/
noncomputable def selectedParentMassPopularCordobaCoreBudget
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (_A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 → Int) (KT : ENNReal) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  ((loss : ENNReal) * (P.length : ENNReal) *
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
    (((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) * 2) *
      (KT * volume
        (selectedParentBucketNormalizedJohnContainer
          S hrho P k r label : Set Space))

/-- The selected source mass times the actual Córdoba core is bounded by a
fully division-free expression.  The same selected block still realizes the
actual outer/fine multiplicity product. -/
theorem exists_massPopularGreedyBlock_crossMultipliedCordobaCore
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) :
    ∃ k : Fin (blocks S.activeCoarseFamily P).length,
      0 < volume (sourceFineLevelShading A (some k)).shadedUnion ∧
      A.refinement.shading.averageMultiplicity ≤
        ((greedyParentFactorization S P).inducedShading
          A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A (some k)).averageMultiplicity ∧
      ∃ label : Fin 3 → Int,
        label ∈ occupiedWeightBuckets
          (Finset.univ : Finset
            {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
          (fun p => sideShapeLabel
            (selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ∧
        0 < bucketShortA label ∧
        bucketShortA label ≤ bucketShortB label ∧
        bucketShortB label ≤ 1 ∧
        (affineJacobian
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label) *
          (IndexedShadingRefinement.restrictTo
            (parentAggregatedShading S D.shading)
            (greedyParentFactorization S P).index.fine).shading.shadingMass) *
            selectedParentFineLevelCordobaCore
              D S hrho P k r hr A label KT ≤
          selectedParentMassPopularCordobaCoreBudget
            D S hrho P k r hr A label KT := by
  obtain ⟨k, _hmass, hvolume, hproduct, label, hoccupied,
      hbucketRetention, ha, hab, hb, _hplank⟩ :=
    exists_massPopularGreedyBlock_actualAverage_and_affinePlankBucket
      D hD S hrho hrhoOne P r hr A hsource
  refine ⟨k, hvolume, hproduct, label, hoccupied, ha, hab, hb, ?_⟩
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  let count : ENNReal :=
    ((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) * 2
  have hbucket0 : Ybucket.shadingMass ≠ 0 := by
    intro hzero
    have hleft0 :
        affineJacobian (bucketNormalizedAffineEquiv e label) *
          (IndexedShadingRefinement.restrictTo
            (parentAggregatedShading S D.shading)
            (greedyParentFactorization S P).index.fine).shading.shadingMass ≠
          0 := by
      exact mul_ne_zero
        (affineJacobian_pos (bucketNormalizedAffineEquiv e label)).ne'
        hsource
    apply hleft0
    have hle0 :
        affineJacobian (bucketNormalizedAffineEquiv e label) *
          (IndexedShadingRefinement.restrictTo
            (parentAggregatedShading S D.shading)
            (greedyParentFactorization S P).index.fine).shading.shadingMass ≤
          0 := by
      calc
        _ ≤ ((loss : ENNReal) * (P.length : ENNReal)) *
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              Ybucket.shadingMass := by
          simpa only [e, B, Ylevel, Ybucket] using hbucketRetention
        _ = 0 := by rw [hzero, mul_zero]
    exact bot_unique hle0
  have hbucketTop : Ybucket.shadingMass ≠ ∞ :=
    Ybucket.shadingMass_lt_top.ne
  have hindices :
      (selectedParentPlankBucketIndices e S B hrho label).Nonempty := by
    obtain ⟨p, hp, hlabel⟩ :=
      mem_occupiedWeightBuckets_iff.mp hoccupied
    refine ⟨p, ?_⟩
    rw [selectedParentPlankBucketIndices, mem_sideShapeBucket_iff]
    exact ⟨Finset.mem_univ _, hlabel⟩
  have hcardPos :
      0 < ((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr hindices
  have hcount0 : count ≠ 0 := by
    dsimp only [count]
    exact mul_ne_zero hcardPos.ne' (by norm_num)
  have hcountTop : count ≠ ∞ := by
    dsimp only [count]
    exact ENNReal.mul_ne_top (by simp) (by norm_num)
  have hcore := massRetention_mul_cordobaQuotient_le hbucketRetention
    hbucket0 hbucketTop hcount0 hcountTop
    (KT := KT)
    (containerVolume := volume
      (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space))
  rw [selectedParentFineLevelCordobaCore_eq_containerVolume_div_mean]
  simpa only [selectedParentFineLevelBucketMeanCarrierMass, Ybucket, count,
    selectedParentMassPopularCordobaCoreBudget] using hcore

#print axioms massRetention_mul_cordobaQuotient_le
#print axioms selectedParentMassPopularCordobaCoreBudget
#print axioms exists_massPopularGreedyBlock_crossMultipliedCordobaCore

end

end Family8SelectedParentMassPopularCordobaCoreV2
