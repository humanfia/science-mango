import Family8Grounding.Family8FullRefinementSourceTauAdaptiveCardWeightedThickLossPowerEndpointV2
import Family8Grounding.Family8FullRefinementSourceTauAdaptiveCardWeightedPowerDichotomyV1

/-!
# Actual hull-thin or same-selected honest Equation (45)/(46) product

The existing source-tau geometry supplies either a literal paper hull-thin
bucket or the uniform power residual.  In the second branch the SAFE thin
adapter constructs the card-weighted budget and uses Equation (45) on the
same selected bucket, retaining its genuine thickening and outer losses.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauAdaptiveCardWeightedThickLossPowerDichotomyV1

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
open Family8FullRefinementSourceTauAdaptiveCardWeightedPowerDichotomyV1
open Family8FullRefinementSourceTauAdaptiveCardWeightedThickLossPowerEndpointV2
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
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
set_option linter.defProp false

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

/-- Callback-free actual dichotomy: paper hull-thin, or the honest
same-selected Equation (45)/(46) product generated from the power residual. -/
noncomputable def sourceTauPaperHullThinOrPowerThickLossEq45CardWeightedEq46
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    (hstoppingEpsilon : 0 < stoppingEpsilon)
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
    (hetaF : 0 ≤ etaF) (hetaKT : 0 < etaKT)
    (habsorbEta : 0 < absorbEta) (hepsilon : 0 ≤ epsilon)
    (hbetaStrict : beta < 2 / 3)
    (hlossEta : 0 < lossEta)
    (hlossExponent : 0 ≤ lossExponent)
    (hcoarseKTExponent : 0 ≤ coarseKTExponent)
    (hinnerKTExponent : 0 ≤ innerKTExponent)
    (hscaleSmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta
        constantAbsorbExponent)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices
        (canonicalUpperPartition
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) U Pgreedy)
        (selected U I)} beta)
    (lemmaEpsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon)
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
          (lossEta / 4)) :=
  Or.imp_right
    (fun hresidual =>
      sourceTauPowerThickLossEq45CardWeightedEq46
        D hD Cmulti Sseq W U Pgreedy A Wouter I r hr hsource
        KT C CKT hKT hKTEvery htauExponent hloss hCKTPower hKTPower
        hconstantAbsorbExponent hfixedSmall hFsource hKTsource
        hetaKT habsorbEta H lemmaEpsilon hlemmaEpsilon hlossEta
        htauHalf htauThreshold hsideThreshold hangleThreshold hresidual)
    (fullRefinement_sourceTau_exists_occupied_paperHullThin_or_forall_powerResidual
      (etaF := etaF) (etaKT := etaKT) (lossEta := lossEta)
      (absorbEta := absorbEta) (epsilon := epsilon) (beta := beta)
      (lossExponent := lossExponent)
      (coarseKTExponent := coarseKTExponent)
      (innerKTExponent := innerKTExponent)
      (constantAbsorbExponent := constantAbsorbExponent)
      D hD Cmulti Sseq W hstoppingEpsilon Pgreedy r hr C
      hetaF hepsilon hbetaStrict hetaKT hlossEta habsorbEta
      hlossExponent hcoarseKTExponent hinnerKTExponent
      hconstantAbsorbExponent hscaleSmall)

#print axioms sourceTauPaperHullThinOrPowerThickLossEq45CardWeightedEq46

end
end Family8FullRefinementSourceTauAdaptiveCardWeightedThickLossPowerDichotomyV1
