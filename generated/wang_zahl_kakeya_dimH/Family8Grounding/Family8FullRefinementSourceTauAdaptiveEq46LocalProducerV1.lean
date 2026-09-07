import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46ThickLossEndpointV1
import Family8Grounding.Family8FullRefinementSourceTauMassPopularEq46LogAbsorbedV3
import Mathlib.Tactic

/-!
# Actual full-refinement source-tau producer for the V17 local Eq. (46) input

This adapter has no multiplicity callback.  It turns the explicit residual
scale/card/Jacobian scalar into the exact local `MassPopularCrossEq46Budget`
for every occupied actual bucket, with the same adaptive full-fibre cap used
by the selected-bucket endpoint.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauAdaptiveEq46LocalProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8FullRefinementActualDatumV1
open Family8FullRefinementSourceTauMassPopularEq46LogAbsorbedV3.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

/-- The exact `hEq46Local` consumed by V17 and by the honest thick-loss
successor, constructed from the paper's remaining explicit residual scalar. -/
theorem fullRefinement_sourceTau_adaptiveEq46Local_of_residualScalar
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
    (KT adaptiveC : ENNReal)
    {etaF etaKT lossEta absorbEta epsilon beta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaKT : 0 < etaKT) (habsorbEta : 0 < absorbEta)
    (htauThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hscalar : ∀ k label,
      ActualSelectedParentBucketOccupied
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy k r hr label →
      (ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) *
        ((Sseq.tau W.m : ENNReal) ^ (-(lossEta + absorbEta)) *
          ((loss : ENNReal) * (Pgreedy.length : ENNReal) *
            (selectedParentPlankBucketIndices
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
              (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)) label).card *
            KT)) ≤
        (((delta : ENNReal) / (Sseq.tau W.m : ENNReal)) ^ 2) *
          ((delta : ENNReal) ^ (2 * etaF) *
            proposition66AInnerFactor (Sseq.tau W.m)
              (bucketShortA label) (bucketShortB label)
              (centeredAdaptiveActualBucketFullFiberNatCap
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
                Pgreedy k r hr label adaptiveC)
              epsilon beta)) :
    ∀ k label,
      ActualSelectedParentBucketOccupied
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy k r hr label →
      MassPopularCrossEq46Budget
        (fullRefinementDatum D)
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        Pgreedy k r hr A label KT lossEta
        (centeredAdaptiveActualBucketFullFiberNatCap
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy k r hr label adaptiveC) epsilon beta := by
  intro k label hoccupied
  exact fullRefinement_sourceTau_massPopularCrossEq46Budget_of_residualScalar
    D hD Cmulti Sseq W Pgreedy k r hr A label KT
    (centeredAdaptiveActualBucketFullFiberNatCap
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      Pgreedy k r hr label adaptiveC)
    hFsource hKTsource hetaKT habsorbEta htauThreshold
    (hscalar k label hoccupied)

#print axioms
  fullRefinement_sourceTau_adaptiveEq46Local_of_residualScalar

end
end Family8FullRefinementSourceTauAdaptiveEq46LocalProducerV1
