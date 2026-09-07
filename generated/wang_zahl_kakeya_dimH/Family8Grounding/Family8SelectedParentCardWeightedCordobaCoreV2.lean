import Family8Grounding.Family8CardWeightedCordobaCancellationAlgebraV1
import Family8Grounding.Family8SelectedParentCardWeightedFineLevelBucketV1
import Family8Grounding.Family8SelectedParentMassPopularEq46CardBudgetV2
import Mathlib.Tactic

/-!
# One-count selected-parent Cordoba core, V2

The card-weighted actual greedy block retains the source with its block
cardinality on the left.  The literal side bucket is a subset of that block,
so its Cordoba count cancels against this weight.  The resulting core budget
contains only the total active-parent cardinality.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentCardWeightedCordobaCoreV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CardWeightedCordobaCancellationAlgebraV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCardWeightedFineLevelBucketV1
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
open Family8SelectedParentMassPopularEq46CardBudgetV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The one-count core budget after exact block/bucket cardinality
cancellation. -/
noncomputable def selectedParentCardWeightedCordobaCoreBudget
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) {loss : Nat}
    (_A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 → Int) (KT : ENNReal) : ENNReal :=
  (((loss : ENNReal) *
      (Fintype.card (ActiveParentIndex S) : ENNReal)) *
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) * 2) *
    (KT * volume
      (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space))

/-- The actual source factor times the literal Cordoba quotient is bounded by
the one-count budget.  The same selected block realizes the actual-average
product. -/
theorem exists_cardWeightedGreedyBlock_crossMultipliedCordobaCore
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
          selectedParentCardWeightedCordobaCoreBudget
            D S hrho P k r A label KT := by
  obtain ⟨k, _hmass, hvolume, hproduct, label, hoccupied,
      hbucketRetention, ha, hab, hb, _hplank⟩ :=
    exists_cardWeightedGreedyBlock_actualAverage_and_affinePlankBucket
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
  let block : ENNReal := (B.card : ENNReal)
  have hretained :
      (affineJacobian (bucketNormalizedAffineEquiv e label) *
        (IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass) *
          block ≤
        (((loss : ENNReal) *
            (Fintype.card (ActiveParentIndex S) : ENNReal)) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
            Ybucket.shadingMass := by
    simpa only [e, B, Ylevel, Ybucket, block] using hbucketRetention
  have hblock0 : block ≠ 0 := by
    dsimp only [block, B]
    exact_mod_cast Finset.card_ne_zero.mpr
      (blockAt S.activeCoarseFamily P k).fiber_nonempty
  have hblockTop : block ≠ ∞ := by
    dsimp only [block]
    exact ENNReal.coe_ne_top
  have hbucket0 : Ybucket.shadingMass ≠ 0 := by
    intro hzero
    have hleft0 :
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (IndexedShadingRefinement.restrictTo
            (parentAggregatedShading S D.shading)
            (greedyParentFactorization S P).index.fine).shading.shadingMass) *
              block ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero
          (affineJacobian_pos (bucketNormalizedAffineEquiv e label)).ne'
          hsource) hblock0
    have hle0 := hretained
    rw [hzero, mul_zero] at hle0
    exact hleft0 (bot_unique hle0)
  have hbucketTop : Ybucket.shadingMass ≠ ∞ :=
    Ybucket.shadingMass_lt_top.ne
  have hindices :
      (selectedParentPlankBucketIndices e S B hrho label).Nonempty := by
    obtain ⟨p, _hp, hlabel⟩ :=
      mem_occupiedWeightBuckets_iff.mp hoccupied
    refine ⟨p, ?_⟩
    rw [selectedParentPlankBucketIndices, mem_sideShapeBucket_iff]
    exact ⟨Finset.mem_univ _, hlabel⟩
  have hcardPos :
      0 < ((selectedParentPlankBucketIndices e S B hrho label).card :
        ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr hindices
  have hcount0 : count ≠ 0 := by
    dsimp only [count]
    exact mul_ne_zero hcardPos.ne' (by norm_num)
  have hcountTop : count ≠ ∞ := by
    dsimp only [count]
    exact ENNReal.mul_ne_top (by simp) (by norm_num)
  have hbucketCardNat :
      (selectedParentPlankBucketIndices e S B hrho label).card ≤ B.card := by
    exact selectedParentPlankBucketIndices_card_le_block
      D S hrho P k e label
  have hbucketCard :
      ((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) ≤
        block := by
    dsimp only [block]
    exact_mod_cast hbucketCardNat
  have hcount : count ≤ 2 * block := by
    dsimp only [count]
    simpa only [mul_comm] using mul_le_mul' hbucketCard le_rfl
  have hcore := cardWeighted_massRetention_mul_cordobaQuotient_le
    hretained hbucket0 hbucketTop hcount0 hcountTop
    hblock0 hblockTop hcount
    (KT := KT)
    (containerVolume := volume
      (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space))
  rw [selectedParentFineLevelCordobaCore_eq_containerVolume_div_mean]
  simpa only [selectedParentFineLevelBucketMeanCarrierMass, Ybucket, count,
    block, selectedParentCardWeightedCordobaCoreBudget] using hcore

#print axioms selectedParentCardWeightedCordobaCoreBudget
#print axioms exists_cardWeightedGreedyBlock_crossMultipliedCordobaCore

end

end Family8SelectedParentCardWeightedCordobaCoreV2
