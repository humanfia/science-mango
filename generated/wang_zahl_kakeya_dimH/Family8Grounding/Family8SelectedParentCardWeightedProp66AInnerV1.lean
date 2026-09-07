import Family8Grounding.Family8SelectedParentCardWeightedCordobaCoreV2
import Family8Grounding.Family8SelectedParentCardWeightedFineLevelCordobaV1
import Family8Grounding.Family8SelectedParentMassPopularProp66AInnerV4
import Mathlib.Tactic

/-!
# Card-weighted selected fibre and the Proposition 6.6(A) inner factor

The selected block and bucket are literal objects from the same exact
assembly.  Their cardinalities cancel before the Equation (46) comparison,
so the scalar budget contains only one active-parent count.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentCardWeightedProp66AInnerV1

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
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCardWeightedCordobaCoreV2
open Family8SelectedParentCardWeightedFineLevelCordobaV1
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentCordobaCoreGeometryV1
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentLogarithmicCordobaCoreV2
open Family8SelectedParentMassPopularEq46CardBudgetV2
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The exact one-count Equation (46) producer interface. -/
def CardWeightedCrossEq46Budget
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 → Int) (KT : ENNReal)
    (lossEta : Real) (tubesPerPlank : Nat) (epsilon beta : Real) : Prop :=
  (rho : ENNReal) ^ (-lossEta) *
      selectedParentCardWeightedCordobaCoreBudget
        D S hrho P k r A label KT ≤
    selectedParentMassPopularSourceFactor D S hrho P k r hr label *
      proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        tubesPerPlank epsilon beta

/-- A one-count Equation (46) budget bounds the selected fine actual average
by the genuine Proposition 6.6(A) inner factor. -/
theorem exists_cardWeightedGreedyBlock_sourceAverage_le_prop66AInner
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
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
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily)
    {tubesPerPlank : Nat} {epsilon beta lossEta : Real}
    (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        (4 * certifiedPlankThresholdedAngleScaleCap 576)
        (lossEta / 4))
    (hEq46 : ∀ k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) →
      CardWeightedCrossEq46Budget D S hrho P k r hr A label KT
        lossEta tubesPerPlank epsilon beta) :
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
        (sourceFineLevelShading A (some k)).averageMultiplicity ≤
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta := by
  obtain ⟨k, _hmass, hvolume, hproduct, label, _hplank, hoccupied,
      _hretained, hglobal, ha, hab, hb, hfineLog⟩ :=
    exists_cardWeightedGreedyBlock_sourceAverage_le_logarithmicCordoba
      D hD S hrho hrhoOne P r hr A hsource KT hKT
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
  let sourceFactor := selectedParentMassPopularSourceFactor
    D S hrho P k r hr label
  have hsourceFactorEq : sourceFactor =
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        (IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass := by
    rfl
  have hglobal' : sourceFactor * block ≤
      (((loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal)) *
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
          Ybucket.shadingMass := by
    simpa only [sourceFactor, hsourceFactorEq, e, B, Ylevel, Ybucket, block]
      using hglobal
  have hblock0 : block ≠ 0 := by
    dsimp only [block, B]
    exact_mod_cast Finset.card_ne_zero.mpr
      (blockAt S.activeCoarseFamily P k).fiber_nonempty
  have hblockTop : block ≠ ∞ := by
    dsimp only [block]
    exact ENNReal.coe_ne_top
  have hbucket0 : Ybucket.shadingMass ≠ 0 := by
    intro hzero
    have hsourceFactor0 : sourceFactor ≠ 0 := by
      rw [hsourceFactorEq]
      exact mul_ne_zero
        (affineJacobian_pos (bucketNormalizedAffineEquiv e label)).ne'
        hsource
    have hleft0 : sourceFactor * block ≠ 0 :=
      mul_ne_zero hsourceFactor0 hblock0
    have hle0 := hglobal'
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
      (selectedParentPlankBucketIndices e S B hrho label).card ≤ B.card :=
    selectedParentPlankBucketIndices_card_le_block D S hrho P k e label
  have hbucketCard :
      ((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) ≤
        block := by
    dsimp only [block]
    exact_mod_cast hbucketCardNat
  have hcount : count ≤ 2 * block := by
    dsimp only [count]
    simpa only [mul_comm] using mul_le_mul' hbucketCard le_rfl
  have hcoreRaw := cardWeighted_massRetention_mul_cordobaQuotient_le
    hglobal' hbucket0 hbucketTop hcount0 hcountTop
    hblock0 hblockTop hcount
    (KT := KT)
    (containerVolume := volume
      (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space))
  have hcore : sourceFactor *
        selectedParentFineLevelCordobaCore
          D S hrho P k r hr A label KT ≤
      selectedParentCardWeightedCordobaCoreBudget
        D S hrho P k r A label KT := by
    rw [selectedParentFineLevelCordobaCore_eq_containerVolume_div_mean]
    simpa only [selectedParentFineLevelBucketMeanCarrierMass, Ybucket, count,
      block, selectedParentCardWeightedCordobaCoreBudget] using hcoreRaw
  have hsourceFactor0 : sourceFactor ≠ 0 := by
    rw [hsourceFactorEq]
    exact mul_ne_zero
      (affineJacobian_pos (bucketNormalizedAffineEquiv e label)).ne'
      hsource
  have hsourceFactorTop : sourceFactor ≠ ∞ := by
    rw [hsourceFactorEq]
    exact ENNReal.mul_ne_top (affineJacobian_ne_top _)
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass_lt_top.ne
  have hscaled : sourceFactor *
        ((rho : ENNReal) ^ (-lossEta) *
          selectedParentFineLevelCordobaCore
            D S hrho P k r hr A label KT) ≤
      sourceFactor * proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        tubesPerPlank epsilon beta := by
    calc
      sourceFactor * ((rho : ENNReal) ^ (-lossEta) *
          selectedParentFineLevelCordobaCore
            D S hrho P k r hr A label KT) =
        (rho : ENNReal) ^ (-lossEta) *
          (sourceFactor * selectedParentFineLevelCordobaCore
            D S hrho P k r hr A label KT) := by ac_rfl
      _ ≤ (rho : ENNReal) ^ (-lossEta) *
          selectedParentCardWeightedCordobaCoreBudget
            D S hrho P k r A label KT := mul_le_mul' le_rfl hcore
      _ ≤ sourceFactor * proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta := by
        simpa only [CardWeightedCrossEq46Budget, sourceFactor] using
          hEq46 k label hoccupied
  have hinnerCore :
      (rho : ENNReal) ^ (-lossEta) *
          selectedParentFineLevelCordobaCore
            D S hrho P k r hr A label KT ≤
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta := by
    apply (ENNReal.mul_le_mul_iff_left
      hsourceFactor0 hsourceFactorTop).mp
    simpa only [mul_comm] using hscaled
  exact hfineLog.trans
    ((selectedParentFineLevelLogarithmicCordobaRHS_le_rpow_mul_core
      D S hrho hrhoHalf P k r hr A label KT hlossEta
      hsideThreshold hangleThreshold).trans hinnerCore)

#print axioms CardWeightedCrossEq46Budget
#print axioms exists_cardWeightedGreedyBlock_sourceAverage_le_prop66AInner

end

end Family8SelectedParentCardWeightedProp66AInnerV1
