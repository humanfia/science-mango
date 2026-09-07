import Family8Grounding.Family8FullRefinementSourceTauCardWeightedEq46CardScaleMassV4
import Family8Grounding.Family8SelectedParentCardWeightedProp66AEndpointV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauCardWeightedProp66AEndpointV1

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
open Family8FullRefinementSourceTauMassPopularEq46ExactCapV4.Witness
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCardWeightedProp66AEndpointV1
open Family8SelectedParentCardWeightedProp66AInnerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Full-refinement source-to-tau card-weighted Proposition 6.6(A)

This specialization composes the exact source-fibre-cap cancellation, the
active-parent card-scale-mass cancellation, and the card-weighted inner/outer
product on the literal `tauScaleCover`.  The only quantitative inner input
left is the division-free scalar displayed below.  Nonzero source mass is
derived from the exact Frostman floor rather than assumed.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

theorem exists_sourceTau_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_cardWeightedScalar
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
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily)
    {plankCount tubesPerPlank : Nat}
    {CF CKT countLoss : ENNReal}
    {etaF etaKT lossEta absorbEta epsilon beta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaKT : 0 < etaKT) (habsorbEta : 0 < absorbEta)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hlossEta : 0 < lossEta)
    (htauHalf : Sseq.tau W.m ≤ (2 : NNReal)⁻¹)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (htauCardThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hsideThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          1 (lossEta / 2))
    (hangleThreshold :
      Sseq.tau W.m / 2 ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          (4 * certifiedPlankThresholdedAngleScaleCap 576)
          (lossEta / 4))
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) ≤
      countLoss *
        (Fintype.card (ActiveParentIndex
          (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)) : ENNReal))
    (houter : ∀ k label,
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
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)) p)) →
      ((greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        Pgreedy).inducedShading A.refinement.shading).averageMultiplicity ≤
        proposition66AOuterFactor (Sseq.tau W.m)
          (bucketShortA label) (bucketShortB label)
          plankCount CF epsilon beta)
    (hscalar : ∀ k label,
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
            (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)) p)) →
      ((ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) *
        (Sseq.tau W.m : ENNReal) ^ (-(lossEta + absorbEta))) *
          ((loss : ENNReal) * (1024 * CKT) * KT) ≤
      (delta : ENNReal) ^ 2 *
        ((delta : ENNReal) ^ (2 * etaF) *
          proposition66AInnerFactor (Sseq.tau W.m)
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)) :
    ∃ a b : NNReal,
      0 < a ∧ a ≤ b ∧ b ≤ 1 ∧
      A.refinement.shading.averageMultiplicity ≤
        countLoss ^ (1 - beta / 2) *
          ((Family8Prop66AFrostmanAspectGainAlgebraV1.proposition66AFrostmanAspectGain
              a b CF beta * (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS (Sseq.tau W.m)
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
                (fullRefinementDatum D).shading).actualFamilyVolume
              epsilon beta) := by
  let E := fullRefinementDatum D
  let S := tauScaleCover E Cmulti Sseq W
  let hrho : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  have hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S E.shading)
        (greedyParentFactorization S Pgreedy).index.fine).shading.shadingMass ≠
          0 := by
    have hfloor :=
      fullRefinement_sourceTau_greedySource_mass_lower_exactCap
        D hD Cmulti Sseq W Pgreedy hFsource hKTsource
    have hfloorPos : 0 <
        (delta : ENNReal) ^ (2 * etaF) /
          (katzTaoDoubledFiberNatCap delta (Sseq.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) := by
      exact ENNReal.div_pos
        (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
          ENNReal.coe_ne_top).ne'
        ENNReal.coe_ne_top
    exact ne_of_gt (hfloorPos.trans_le
      (by simpa only [E, S] using hfloor))
  apply
    exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_cardWeightedCrossEq46
      E (fullRefinementDatum_isAdmissible hD) S hrho
      (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m) htauHalf
      Pgreedy r hr A hsource KT hKT hbeta hbetaOne hlossEta
      hsideThreshold hangleThreshold hcount
      (by simpa only [E, S, hrho] using houter)
  intro k label hoccupied
  exact fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_cardScaleMass
    D hD Cmulti Sseq W Pgreedy k r hr A label KT tubesPerPlank
      hFsource hKTsource hetaKT habsorbEta htauHalf hKTEvery
      htauCardThreshold (hscalar k label hoccupied)

#print axioms
  exists_sourceTau_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_cardWeightedScalar

end Witness
end
end Family8FullRefinementSourceTauCardWeightedProp66AEndpointV1
