import Family8Grounding.Family8SelectedParentAdaptiveInnerSourcePowerLowerV1
import Family8Grounding.Family8SelectedParentSourceTauAdaptiveScaleReservePowerLowerV1
import Mathlib.Tactic

/-!
# Source-tau actual inner-factor delta power

This composes the source-tau non-hull-thin scale reserve with the actual
source Katz--Tao beta-half reserve on the same selected bucket and local
adaptive cap.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentSourceTauAdaptiveInnerPowerLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveInnerSourcePowerLowerV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentSourceTauAdaptiveScaleReservePowerLowerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {Cmulti : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {stoppingEpsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

theorem selectedParent_sourceTau_nonHullThin_deltaPower_le_adaptiveActualInnerFactor
    (D : IdentifiedFrostmanDividingWitness
      fine Cmulti N stoppingEpsilon eta scaleSequence)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (G : StickyScaleCover fine (scaleSequence.tau D.m))
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks G.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G
          (hdelta.trans_le (scaleSequence.delta_le_tau D.m)) P k) r hr)
      G (blockAt G.activeCoarseFamily P k).fiber
        (hdelta.trans_le (scaleSequence.delta_le_tau D.m)) label})
    (paperTau : Real)
    (hnotHullThin : ¬ hullShortestSide
      (selectedParentGreedyBlockJohnFrame G
        (hdelta.trans_le (scaleSequence.delta_le_tau D.m)) P k) ≤
          scaleSequence.tau D.m ^ (1 - paperTau))
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta (scaleSequence.tau D.m) r label / 8 ≤
        (1 / 100 : NNReal))
    (C : ENNReal) (coarseExponent innerEpsilon beta
      absorbExponent : Real)
    (hKT : IsKatzTao C G.activeCoarseFamily)
    (hCpower : C ≤ (delta : ENNReal) ^ (-coarseExponent))
    (hbeta : 0 ≤ beta) (hbetaTwoThirds : beta ≤ 2 / 3)
    (hflatRadiusExponent :
      -innerEpsilon / 2 + (1 - paperTau) * (2 - 3 * beta) ≤ 0)
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    (delta : ENNReal) ^
        (coarseExponent * (beta / 2) + absorbExponent +
          stoppingEpsilon *
            (-innerEpsilon / 2 +
              (1 - paperTau) * (2 - 3 * beta))) ≤
      proposition66AInnerFactor (scaleSequence.tau D.m)
        (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveActualBucketFullFiberNatCap G
          (hdelta.trans_le (scaleSequence.delta_le_tau D.m))
          P k r hr label C) innerEpsilon beta := by
  let rho := scaleSequence.tau D.m
  let hrho : 0 < rho := hdelta.trans_le (scaleSequence.delta_le_tau D.m)
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame G hrho P k) r hr
  let B := (blockAt G.activeCoarseFamily P k).fiber
  have hWmem : (W.1 : {p // p ∈ B}) ∈
      selectedParentPlankBucketIndices e G B hrho label := by
    simpa only [rho, hrho, e, B] using W.2
  have hWshape : sideShapeLabel
      (selectedParentLongRelabeledSide e G B hrho W.1) = label := by
    change (W.1 : {p // p ∈ B}) ∈ sideShapeBucket Finset.univ
      (fun p => selectedParentLongRelabeledSide e G B hrho p) label at hWmem
    exact (mem_sideShapeBucket_iff _ _ _ _).mp hWmem |>.2
  have hoccupied : SelectedBucketOccupied G hrho P k r hr label := by
    rw [SelectedBucketOccupied]
    exact mem_occupiedWeightBuckets_iff.mpr
      ⟨W.1, Finset.mem_univ _, hWshape⟩
  let p : Real := coarseExponent * (beta / 2)
  let s : Real := absorbExponent + stoppingEpsilon *
    (-innerEpsilon / 2 + (1 - paperTau) * (2 - 3 * beta))
  let R : ENNReal :=
    (rho : ENNReal) ^ (-innerEpsilon / 2) *
      ((bucketShortB label : ENNReal) /
        (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * beta))
  let inner : ENNReal := proposition66AInnerFactor rho
    (bucketShortA label) (bucketShortB label)
    (centeredAdaptiveActualBucketFullFiberNatCap G hrho
      P k r hr label C) innerEpsilon beta
  have hscale : (delta : ENNReal) ^ s ≤ R := by
    simpa only [rho, hrho, s, R] using
      selectedParent_sourceTau_nonHullThin_scaleReservePowerLower
        D hfineContained hdelta G P k r hr label W paperTau
        innerEpsilon beta absorbExponent hnotHullThin hbetaTwoThirds
        hflatRadiusExponent habsorbExponent hsmall
  have hinner : (delta : ENNReal) ^ p * R ≤ inner := by
    simpa only [rho, hrho, p, R, inner] using
      selectedParent_deltaBetaHalf_mul_scaleReserve_le_adaptiveActualInnerFactor
        G hrho P k r hr label hoccupied hdelta hdeltaHalf hsmallPacking
        C coarseExponent innerEpsilon beta hKT hCpower hbeta
          (hbetaTwoThirds.trans (by norm_num))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (delta : ENNReal) ^
        (coarseExponent * (beta / 2) + absorbExponent +
          stoppingEpsilon *
            (-innerEpsilon / 2 +
              (1 - paperTau) * (2 - 3 * beta))) =
      (delta : ENNReal) ^ p * (delta : ENNReal) ^ s := by
        rw [← ENNReal.rpow_add p s hd0 hdTop]
        congr 1
        dsimp only [p, s]
        ring
    _ ≤ (delta : ENNReal) ^ p * R := mul_le_mul' le_rfl hscale
    _ ≤ inner := hinner
    _ = proposition66AInnerFactor (scaleSequence.tau D.m)
        (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveActualBucketFullFiberNatCap G
          (hdelta.trans_le (scaleSequence.delta_le_tau D.m))
          P k r hr label C) innerEpsilon beta := rfl

#print axioms
  selectedParent_sourceTau_nonHullThin_deltaPower_le_adaptiveActualInnerFactor

end
end Family8SelectedParentSourceTauAdaptiveInnerPowerLowerV1
