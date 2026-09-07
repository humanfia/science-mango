import Family8Grounding.Family8FullRefinementSourceTauAdaptiveCardWeightedPowerEndpointV1

/-!
# Source-tau power residual produces the actual card-weighted budget

This thin lemma isolates the only scalar calculation used by the larger
same-selected endpoint.  Its conclusion is the actual one-bucket
`CardWeightedCrossEq46Budget`; it does not package the conclusion as an input.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauAdaptiveCardWeightedPowerBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CardWeightedEq46CoefficientPowerEnvelopeV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8FullRefinementActualDatumV1
open Family8FullRefinementSourceTauCardWeightedEq46CardScaleMassV4.Witness
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCardWeightedProp66AInnerV1
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

/-- The complete coefficient power envelope, followed by the actual
source-tau card/scale/mass cancellation, at one literal bucket. -/
theorem fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_powerResidual
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
    (k : Fin (blocks
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
      Pgreedy).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) Pgreedy)
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (fullRefinementDatum D).shading) loss)
    (label : Fin 3 → Int) (KT : ENNReal) (tubesPerPlank : Nat)
    (CKT : ENNReal)
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
    (htauHalf : Sseq.tau W.m ≤ (2 : NNReal)⁻¹)
    (htauThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hpowerResidual :
      (delta : ENNReal) ^
        (-(etaKT + (lossEta + absorbEta) + lossExponent +
          coarseKTExponent + innerKTExponent + constantAbsorbExponent)) ≤
        (delta : ENNReal) ^ 2 *
          ((delta : ENNReal) ^ (2 * etaF) *
            proposition66AInnerFactor (Sseq.tau W.m)
              (bucketShortA label) (bucketShortB label)
              tubesPerPlank epsilon beta)) :
    CardWeightedCrossEq46Budget
      (fullRefinementDatum D)
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      Pgreedy k r hr A label KT lossEta tubesPerPlank epsilon beta := by
  have hcoefficient :=
    cardWeightedEq46Coefficient_le_delta_negativePower
      (delta := delta) (tau := Sseq.tau W.m)
      (loss := (loss : ENNReal)) (CKT := CKT) (KT := KT)
      (etaKT := etaKT) (tauExponent := lossEta + absorbEta)
      (lossExponent := lossExponent)
      (coarseKTExponent := coarseKTExponent)
      (innerKTExponent := innerKTExponent)
      (constantAbsorbExponent := constantAbsorbExponent)
      hD.delta_pos (Sseq.delta_le_tau W.m) htauExponent hloss
      hCKTPower hKTPower hconstantAbsorbExponent hfixedSmall
  exact
    fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_cardScaleMass
      D hD Cmulti Sseq W Pgreedy k r hr A label KT tubesPerPlank
      hFsource hKTsource hetaKT habsorbEta htauHalf hKTEvery
      htauThreshold (hcoefficient.trans hpowerResidual)

#print axioms
  fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_powerResidual

end
end Family8FullRefinementSourceTauAdaptiveCardWeightedPowerBudgetV1
