import Family8Grounding.Family8CardWeightedActiveParentCardScaleCancellationV2
import Family8Grounding.Family8FullRefinementSourceTauCardWeightedEq46LogAbsorbedV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullRefinementSourceTauCardWeightedEq46CardScaleMassV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCardWeightedProp66AInnerV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover
open Family8CardWeightedActiveParentCardScaleCancellationV2
open Family8FullRefinementSourceTauCardWeightedEq46LogAbsorbedV1.Witness

noncomputable section

/-!
# Source-tau Equation (46) after normalized parent-mass cancellation

The one remaining active-parent count in the card-weighted endpoint is paired
with the relative square on its right.  The actual every-scale Katz--Tao
certificate bounds the normalized mass of exactly the same tau-cover by
`1024 * CKT`.  Consequently the scalar premise below contains no raw parent
cardinality and incurs no artificial `tau^-2` loss.

V1--V3 were namespace/association drafts and are deliberately not imported.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}

theorem fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_cardScaleMass
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
    (k : Fin
      (blocks
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W).activeCoarseFamily
        Pgreedy).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W) Pgreedy)
      (parentAggregatedShading
        (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
        (fullRefinementDatum D).shading) loss)
    (label : Fin 3 → Int) (KT : ENNReal)
    (tubesPerPlank : Nat)
    {etaF etaKT lossEta absorbEta epsilon beta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaKT : 0 < etaKT) (habsorbEta : 0 < absorbEta)
    (htauHalf : Sseq.tau W.m ≤ (2 : NNReal)⁻¹)
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (htauThreshold :
      Sseq.tau W.m ≤
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hscalar :
      ((ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) *
        (Sseq.tau W.m : ENNReal) ^ (-(lossEta + absorbEta))) *
          ((loss : ENNReal) * (1024 * CKT) * KT) ≤
      (delta : ENNReal) ^ 2 *
        ((delta : ENNReal) ^ (2 * etaF) *
          proposition66AInnerFactor (Sseq.tau W.m)
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)) :
    CardWeightedCrossEq46Budget
      (fullRefinementDatum D)
      (tauScaleCover (fullRefinementDatum D) Cmulti Sseq W)
      (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      Pgreedy k r hr A label KT lossEta
      tubesPerPlank epsilon beta := by
  let E := fullRefinementDatum D
  let S := tauScaleCover E Cmulti Sseq W
  let hrho : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  have hKTTau : S.IsKatzTaoAtScale CKT := by
    dsimp only [S]
    exact hKTEvery (Sseq.tau W.m) (Sseq.delta_le_tau W.m)
      (CoherentStickyMultiscaleCover.tau_le_one Sseq W.m)
  have hX : (activeCoarseCardScaleMass S : ENNReal) ≤ 1024 * CKT := by
    exact activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale
      E (fullRefinementDatum_isAdmissible hD) S htauHalf hKTTau
  have hcardScalar :
      (ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) *
        ((Sseq.tau W.m : ENNReal) ^ (-(lossEta + absorbEta)) *
          ((loss : ENNReal) *
            (Fintype.card (ActiveParentIndex S) : ENNReal) * KT)) ≤
      (((delta : ENNReal) / (Sseq.tau W.m : ENNReal)) ^ 2) *
        ((delta : ENNReal) ^ (2 * etaF) *
          proposition66AInnerFactor (Sseq.tau W.m)
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta) := by
    have hcancel :=
      cardWeighted_activeCoarse_le_relativeSquare_of_cardScaleMass
        S hD.delta_pos hrho hX hscalar
    simpa only [Fintype.card_coe, mul_assoc] using hcancel
  exact
    fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_residualScalar
      D hD Cmulti Sseq W Pgreedy k r hr A label KT tubesPerPlank
      hFsource hKTsource hetaKT habsorbEta htauThreshold
      (by simpa only [E, S, hrho] using hcardScalar)

#print axioms
  fullRefinement_sourceTau_cardWeightedCrossEq46Budget_of_cardScaleMass

end Witness
end
end Family8FullRefinementSourceTauCardWeightedEq46CardScaleMassV4
