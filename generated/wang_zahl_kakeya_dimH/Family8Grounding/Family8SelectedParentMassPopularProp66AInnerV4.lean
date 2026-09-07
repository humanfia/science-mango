import Family8Grounding.Family8SelectedParentMassPopularFineLevelCordobaV3
import Family8Grounding.Family8SelectedParentMassPopularCordobaCoreV2
import Family8Grounding.Family8SelectedParentLogarithmicCordobaCoreV2
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# The mass-popular selected fibre and the Proposition 6.6(A) inner factor

The preceding modules choose one actual mass-popular greedy occurrence and
one literal side bucket on that occurrence.  The same bucket supplies both
the named logarithmic Cordoba bound and source-to-bucket mass retention.

This module cancels the remaining bucket mass and then the positive finite
source factor.  Consequently the only input left between the actual Cordoba
geometry and Equation (46) is a division-free, cross-multiplied scalar
inequality involving scales, cardinalities, Katz--Tao mass, and source mass.
It is deliberately named below instead of being hidden as an
average-multiplicity premise.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentMassPopularProp66AInnerV4

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
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAffineShadingTransportV4
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
open Family8SelectedParentMassPopularCordobaCoreV2
open Family8SelectedParentMassPopularFineLevelCordobaV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The positive finite factor which is cancelled after the bucket mass has
been removed. -/
noncomputable def selectedParentMassPopularSourceFactor
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) : ENNReal :=
  affineJacobian
      (bucketNormalizedAffineEquiv
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        label) *
    (IndexedShadingRefinement.restrictTo
      (parentAggregatedShading S D.shading)
      (greedyParentFactorization S P).index.fine).shading.shadingMass

/-- The exact remaining Equation (46) producer interface.  It contains no
multiplicity conclusion and no selected-bucket mass denominator. -/
def MassPopularCrossEq46Budget
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
    (label : Fin 3 -> Int) (KT : ENNReal)
    (lossEta : Real) (tubesPerPlank : Nat) (epsilon beta : Real) : Prop :=
  (rho : ENNReal) ^ (-lossEta) *
      selectedParentMassPopularCordobaCoreBudget
        D S hrho P k r hr A label KT <=
    selectedParentMassPopularSourceFactor D S hrho P k r hr label *
      proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        tubesPerPlank epsilon beta

/-- Once the division-free Equation (46) budget is available for actual
occupied buckets, the mass-popular selector returns one surviving fine
factor bounded by the genuine Proposition 6.6(A) inner factor. -/
theorem exists_massPopularGreedyBlock_sourceAverage_le_prop66AInner
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
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
      rho <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        (4 * certifiedPlankThresholdedAngleScaleCap 576)
        (lossEta / 4))
    (hEq46 : forall k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ->
      MassPopularCrossEq46Budget D S hrho P k r hr A label KT
        lossEta tubesPerPlank epsilon beta) :
    ∃ k : Fin (blocks S.activeCoarseFamily P).length,
      0 < volume (sourceFineLevelShading A (some k)).shadedUnion ∧
      A.refinement.shading.averageMultiplicity <=
        ((greedyParentFactorization S P).inducedShading
          A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A (some k)).averageMultiplicity ∧
      ∃ label : Fin 3 -> Int,
        label ∈ occupiedWeightBuckets
          (Finset.univ : Finset
            {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
          (fun p => sideShapeLabel
            (selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ∧
        0 < bucketShortA label ∧
        bucketShortA label <= bucketShortB label ∧
        bucketShortB label <= 1 ∧
        (sourceFineLevelShading A (some k)).averageMultiplicity <=
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta := by
  obtain ⟨k, _hmass, hvolume, hproduct, label, _hplank, hoccupied,
      _hretained, hglobal, ha, hab, hb, hfineLog⟩ :=
    exists_massPopularGreedyBlock_sourceAverage_le_logarithmicCordoba
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
  let sourceFactor := selectedParentMassPopularSourceFactor
    D S hrho P k r hr label
  have hsourceFactorEq : sourceFactor =
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        (IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass := by
    rfl
  have hbucket0 : Ybucket.shadingMass ≠ 0 := by
    intro hzero
    have hleft0 : sourceFactor ≠ 0 := by
      rw [hsourceFactorEq]
      exact mul_ne_zero
        (affineJacobian_pos (bucketNormalizedAffineEquiv e label)).ne'
        hsource
    apply hleft0
    have hle0 : sourceFactor <= 0 := by
      rw [hsourceFactorEq]
      calc
        _ <= ((loss : ENNReal) * (P.length : ENNReal)) *
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              Ybucket.shadingMass := by
          simpa only [e, B, Ylevel, Ybucket] using hglobal
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
      0 < ((selectedParentPlankBucketIndices e S B hrho label).card :
        ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr hindices
  have hcount0 : count ≠ 0 := by
    dsimp only [count]
    exact mul_ne_zero hcardPos.ne' (by norm_num)
  have hcountTop : count ≠ ∞ := by
    dsimp only [count]
    exact ENNReal.mul_ne_top (by simp) (by norm_num)
  have hcoreRaw := massRetention_mul_cordobaQuotient_le hglobal
    hbucket0 hbucketTop hcount0 hcountTop
    (KT := KT)
    (containerVolume := volume
      (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space))
  have hcore : sourceFactor *
        selectedParentFineLevelCordobaCore
          D S hrho P k r hr A label KT <=
      selectedParentMassPopularCordobaCoreBudget
        D S hrho P k r hr A label KT := by
    rw [selectedParentFineLevelCordobaCore_eq_containerVolume_div_mean]
    rw [hsourceFactorEq]
    simpa only [selectedParentFineLevelBucketMeanCarrierMass, Ybucket, count,
      selectedParentMassPopularCordobaCoreBudget] using hcoreRaw
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
            D S hrho P k r hr A label KT) <=
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
      _ <= (rho : ENNReal) ^ (-lossEta) *
          selectedParentMassPopularCordobaCoreBudget
            D S hrho P k r hr A label KT :=
        mul_le_mul' le_rfl hcore
      _ <= sourceFactor * proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta := by
        simpa only [MassPopularCrossEq46Budget, sourceFactor] using
          hEq46 k label hoccupied
  have hinnerCore :
      (rho : ENNReal) ^ (-lossEta) *
          selectedParentFineLevelCordobaCore
            D S hrho P k r hr A label KT <=
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta :=
    by
      apply (ENNReal.mul_le_mul_iff_left hsourceFactor0 hsourceFactorTop).mp
      simpa only [mul_comm] using hscaled
  exact hfineLog.trans
    ((selectedParentFineLevelLogarithmicCordobaRHS_le_rpow_mul_core
      D S hrho hrhoHalf P k r hr A label KT hlossEta
      hsideThreshold hangleThreshold).trans hinnerCore)

#print axioms selectedParentMassPopularSourceFactor
#print axioms MassPopularCrossEq46Budget
#print axioms exists_massPopularGreedyBlock_sourceAverage_le_prop66AInner

end

end Family8SelectedParentMassPopularProp66AInnerV4
