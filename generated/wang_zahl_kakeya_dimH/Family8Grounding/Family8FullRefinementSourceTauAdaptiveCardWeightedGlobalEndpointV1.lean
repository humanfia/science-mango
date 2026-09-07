import Family8Grounding.Family8FullRefinementSourceTauCardWeightedEq46CardScaleMassV4
import Family8Grounding.Family8SelectedParentCardWeightedProp66AEndpointV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauAdaptiveCardWeightedGlobalEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8FullRefinementActualDatumV1
open Family8FullRefinementSourceTauCardWeightedEq46CardScaleMassV4.Witness
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentCardWeightedProp66AEndpointV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Canonical card-weighted source-tau scalar to the adaptive global endpoint

The card-weighted cancellation removes the greedy length and bucket-card
factors from the mass-popular residual.  This adapter instantiates the existing
one-count Eq. (46) producer with the finite global adaptive cap and sends it to
the actual Prop. 6.6(A) count-loss consumer.  It introduces no callback and no
target inequality packaged in a structure.
-/

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

theorem exists_refinementAverage_le_adaptiveGlobalCap_mul_actualFrostmanRHS_of_cardWeightedScalar
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    (Pgreedy : GreedyDensityPartition
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W))))
      (hullContainer
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
      Finset.univ)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) Pgreedy)
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (fullRefinementDatum D).shading) loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (fullRefinementDatum D).shading)
        (greedyParentFactorization
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          Pgreedy).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
    (C CF CKT : ENNReal) {etaF etaKT lossEta absorbEta epsilon beta : Real}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaKT : 0 < etaKT) (habsorbEta : 0 < absorbEta)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hlossEta : 0 < lossEta)
    (htauHalf : Sseq.tau W.m <= (2 : NNReal)⁻¹)
    (htauThreshold :
      Sseq.tau W.m <=
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hsideThreshold :
      Sseq.tau W.m <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      Sseq.tau W.m / 2 <=
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          (4 * certifiedPlankThresholdedAngleScaleCap 576)
          (lossEta / 4))
    (houter : forall k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt
            (tauScaleCover
              (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
            Pgreedy k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                Pgreedy k) r hr)
            (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
            (blockAt
              (tauScaleCover
                (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
              Pgreedy k).fiber
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)) p)) ->
      ((greedyParentFactorization
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) Pgreedy)
        |>.inducedShading A.refinement.shading).averageMultiplicity <=
          proposition66AOuterFactor (Sseq.tau W.m)
            (bucketShortA label) (bucketShortB label)
            (Fintype.card (ActiveParentIndex
              (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)))
            CF epsilon beta)
    (hscalar : forall k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt
            (tauScaleCover
              (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
            Pgreedy k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                Pgreedy k) r hr)
            (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
            (blockAt
              (tauScaleCover
                (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
              Pgreedy k).fiber
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)) p)) ->
      ((ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) *
        (Sseq.tau W.m : ENNReal) ^ (-(lossEta + absorbEta))) *
          ((loss : ENNReal) * (1024 * CKT) * KT) <=
        (delta : ENNReal) ^ 2 *
          ((delta : ENNReal) ^ (2 * etaF) *
            proposition66AInnerFactor (Sseq.tau W.m)
              (bucketShortA label) (bucketShortB label)
              (centeredAdaptiveGlobalFullFiberNatCap
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                Pgreedy r hr C)
              epsilon beta)) :
    exists a b : NNReal,
      0 < a ∧ a <= b ∧ b <= 1 ∧
      A.refinement.shading.averageMultiplicity <=
        (centeredAdaptiveGlobalFullFiberNatCap
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy r hr C : ENNReal) ^ (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain a b CF beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS (Sseq.tau W.m)
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (fullRefinementDatum D).shading).actualFamilyVolume
              epsilon beta) := by
  apply
    exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_cardWeightedCrossEq46
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m)
      htauHalf Pgreedy r hr A hsource KT hKT
      (plankCount := Fintype.card (ActiveParentIndex
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)))
      (tubesPerPlank := centeredAdaptiveGlobalFullFiberNatCap
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy r hr C)
      (CF := CF)
      (countLoss := (centeredAdaptiveGlobalFullFiberNatCap
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy r hr C : ENNReal))
      hbeta hbetaOne hlossEta hsideThreshold hangleThreshold
      (selectedParent_centeredAdaptive_globalEq46Count
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy r hr C)
      houter
  intro k label hoccupied
  exact
    fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_cardScaleMass
      D hD Cmulti Sseq W Pgreedy k r hr A label KT
      (centeredAdaptiveGlobalFullFiberNatCap
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy r hr C)
      hFsource hKTsource hetaKT habsorbEta htauHalf hKTEvery
      htauThreshold (hscalar k label hoccupied)

#print axioms
  exists_refinementAverage_le_adaptiveGlobalCap_mul_actualFrostmanRHS_of_cardWeightedScalar

end
end Family8FullRefinementSourceTauAdaptiveCardWeightedGlobalEndpointV1
