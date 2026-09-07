import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveCardWeightedThickLossEndpointV1
import Family8Grounding.Family8FullRefinementSourceTauAdaptiveCardWeightedPowerBudgetV1

/-!
# Thin source-tau power-residual / same-selected product adapter

The result is inferred from the two SAFE producers, avoiding a second
elaboration of the large dependent Equation (45) conclusion.  Unlike the
failed monolithic draft, this module contains only the actual source-tau
power residual and its literal card-weighted budget producer.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauAdaptiveCardWeightedThickLossPowerEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8CardWeightedEq46CoefficientPowerEnvelopeV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8FullRefinementActualDatumV1
open Family8FullRefinementSourceTauAdaptiveCardWeightedPowerBudgetV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessAdaptiveCardWeightedThickLossEndpointV1
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 30000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

set_option linter.defProp false

/-- Proof-valued composition of the literal one-bucket power-budget producer
with the same-selected Equation (45)/(46) endpoint. -/
noncomputable def sourceTauPowerThickLossEq45CardWeightedEq46
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    {sigma : NNReal}
    (U : StickyScaleCover
      ((tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).coarse.restrictTo
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarse)
      sigma)
    (Pgreedy : GreedyDensityPartition
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
      (hullCandidates (Finset.univ : Finset
        (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W))))
      (hullContainer
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
      Finset.univ)
    {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) Pgreedy)
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (fullRefinementDatum D).shading) loss)
    {conflictLoss : ENNReal}
    (Wouter : DoubledParentConflictWeightedSelection U
      (occurrenceMaxOwnerMass U
        (canonicalUpperPartition
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) U Pgreedy)
        A.refinement.shading Finset.univ) conflictLoss)
    (I : PaperEq45MaxWitnessCommonScaleInput U
      A.refinement.shading Finset.univ conflictLoss Wouter)
    (r : NNReal) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (fullRefinementDatum D).shading)
        (greedyParentFactorization
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          Pgreedy).index.fine).shading.shadingMass ≠ 0)
    (KT C CKT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
    {etaF etaKT lossEta absorbEta epsilon beta : Real}
    {lossExponent coarseKTExponent innerKTExponent
      constantAbsorbExponent : Real}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (htauExponent : 0 ≤ lossEta + absorbEta)
    (hloss : (loss : ENNReal) ≤
      (delta : ENNReal) ^ (-lossExponent))
    (hCKTPower : CKT ≤ (delta : ENNReal) ^ (-coarseKTExponent))
    (hKTPower : KT ≤ (delta : ENNReal) ^ (-innerKTExponent))
    (hconstantAbsorbExponent : 0 < constantAbsorbExponent)
    (hfixedSmall : delta ≤
      cardWeightedEq46FixedConstantThreshold constantAbsorbExponent)
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaKT : 0 < etaKT) (habsorbEta : 0 < absorbEta)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices
        (canonicalUpperPartition
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) U Pgreedy)
        (selected U I)} beta)
    (lemmaEpsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon)
    (hlossEta : 0 < lossEta)
    (htauHalf : Sseq.tau W.m ≤ (2 : NNReal)⁻¹)
    (htauThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hsideThreshold :
      Sseq.tau W.m ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      Sseq.tau W.m / 2 ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          (4 * certifiedPlankThresholdedAngleScaleCap 576)
          (lossEta / 4))
    (hpowerResidual : ∀ k label,
      ActualSelectedParentBucketOccupied
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy k r hr label →
      (delta : ENNReal) ^
        (-(etaKT + (lossEta + absorbEta) + lossExponent +
          coarseKTExponent + innerKTExponent + constantAbsorbExponent)) ≤
        (delta : ENNReal) ^ 2 *
          ((delta : ENNReal) ^ (2 * etaF) *
            proposition66AInnerFactor (Sseq.tau W.m)
              (bucketShortA label) (bucketShortB label)
              (centeredAdaptiveGlobalFullFiberNatCap
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                Pgreedy r hr C)
              epsilon beta)) :=
  exists_family6Parameters_refinementAverage_le_thickLossEq45_mul_cardWeightedEq46
    (fullRefinementDatum D)
    (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
    U Pgreedy A Wouter I (fullRefinementDatum_isAdmissible hD)
    (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
    (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m) htauHalf
    r hr hsource KT hKT
    (centeredAdaptiveGlobalFullFiberNatCap
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)) Pgreedy r hr C)
    H lemmaEpsilon epsilon hlemmaEpsilon hlossEta
    hsideThreshold hangleThreshold
    (fun k label hoccupied =>
      fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_powerResidual
        D hD Cmulti Sseq W Pgreedy k r hr A label KT
        (centeredAdaptiveGlobalFullFiberNatCap
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)) Pgreedy r hr C)
        CKT hKTEvery htauExponent hloss hCKTPower hKTPower
        hconstantAbsorbExponent hfixedSmall hFsource hKTsource
        hetaKT habsorbEta htauHalf htauThreshold
        (hpowerResidual k label hoccupied))

#print axioms sourceTauPowerThickLossEq45CardWeightedEq46

end
end Family8FullRefinementSourceTauAdaptiveCardWeightedThickLossPowerEndpointV2
