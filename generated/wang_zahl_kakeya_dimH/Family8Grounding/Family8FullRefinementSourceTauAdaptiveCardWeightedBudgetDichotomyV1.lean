import Family8Grounding.Family8FullRefinementSourceTauAdaptiveGlobalPowerResidualDichotomyV1
import Family8Grounding.Family8FullRefinementSourceTauAdaptiveCardWeightedPowerBudgetV1

/-!
# Low-beta source-tau hull-thin / card-weighted Equation (46) dichotomy

The canonical source-tau geometric dichotomy already constructs the complete
power residual on every actual occupied bucket in its non-thin branch.  This
thin successor sends that residual directly through the genuine source-tau
card/scale/mass producer.  Thus the second branch is the literal
`CardWeightedCrossEq46Budget` required by the same-selected Equation (45)
consumer; it is not supplied as a premise.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8FullRefinementSourceTauAdaptiveCardWeightedBudgetDichotomyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CardWeightedEq46CoefficientPowerEnvelopeV1
open Family8FullRefinementActualDatumV1
open Family8FullRefinementSourceTauAdaptiveCardWeightedPowerBudgetV1
open Family8FullRefinementSourceTauAdaptiveGlobalPowerResidualDichotomyV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentCardWeightedProp66AInnerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentSourceTauAdaptiveGlobalPowerResidualV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

/-- In the low-`beta` range, either an actual occupied source-tau bucket is
paper hull-thin, or every actual occupied bucket satisfies the literal
card-weighted Equation (46) budget with the canonical global adaptive cap. -/
theorem fullRefinement_sourceTau_exists_occupied_paperHullThin_or_forall_cardWeightedBudget
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N
        stoppingEpsilon stoppingEta Sseq)
    (hstoppingEpsilon : 0 < stoppingEpsilon)
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
    (KT adaptiveC CKT : ENNReal)
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
    (hetaF : 0 ≤ etaF) (hepsilon : 0 ≤ epsilon)
    (hbetaStrict : beta < 2 / 3)
    (hetaKT : 0 < etaKT) (hlossEta : 0 < lossEta)
    (habsorbEta : 0 < absorbEta)
    (hlossExponent : 0 ≤ lossExponent)
    (hcoarseKTExponent : 0 ≤ coarseKTExponent)
    (hinnerKTExponent : 0 ≤ innerKTExponent)
    (htauHalf : Sseq.tau W.m ≤ (2 : NNReal)⁻¹)
    (htauThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hscaleSmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta
        constantAbsorbExponent) :
    let coefficientExponent := etaKT + (lossEta + absorbEta) +
      lossExponent + coarseKTExponent + innerKTExponent +
        constantAbsorbExponent
    let paperTau := selectedParentSourceTauEq46PaperTau stoppingEpsilon
      epsilon beta constantAbsorbExponent coefficientExponent etaF
    (∃ k : Fin (blocks
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
          Pgreedy).length,
      ∃ label : Fin 3 → Int,
        ActualSelectedParentBucketOccupied
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy k r hr label ∧
        hullShortestSide
          (selectedParentGreedyBlockJohnFrame
            (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
            Pgreedy k) ≤
          Sseq.tau W.m ^ (1 - paperTau)) ∨
      (∀ k label,
        ActualSelectedParentBucketOccupied
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy k r hr label →
        CardWeightedCrossEq46Budget
          (fullRefinementDatum D)
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy k r hr A label KT lossEta
          (centeredAdaptiveGlobalFullFiberNatCap
            (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
            Pgreedy r hr adaptiveC)
          epsilon beta) := by
  dsimp only
  obtain hthin | hresidual :=
    fullRefinement_sourceTau_exists_occupied_paperHullThin_or_forall_powerResidual
      D hD Cmulti Sseq W hstoppingEpsilon Pgreedy r hr adaptiveC
      hetaF hepsilon hbetaStrict hetaKT hlossEta habsorbEta
      hlossExponent hcoarseKTExponent hinnerKTExponent
      hconstantAbsorbExponent hscaleSmall
  · exact Or.inl hthin
  · right
    intro k label hoccupied
    exact
      fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_powerResidual
        D hD Cmulti Sseq W Pgreedy k r hr A label KT
        (centeredAdaptiveGlobalFullFiberNatCap
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          Pgreedy r hr adaptiveC)
        CKT hKTEvery htauExponent hloss hCKTPower hKTPower
        hconstantAbsorbExponent hfixedSmall hFsource hKTsource
        hetaKT habsorbEta htauHalf htauThreshold
        (hresidual k label hoccupied)

#print axioms
  fullRefinement_sourceTau_exists_occupied_paperHullThin_or_forall_cardWeightedBudget

end
end Family8FullRefinementSourceTauAdaptiveCardWeightedBudgetDichotomyV1
