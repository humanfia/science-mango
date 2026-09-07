import Family8Grounding.Family8NormalizedLongIntervalRelevantDef212InputsV5
import Family8Grounding.Family8ParameterLadderFourSeparationThresholdV1
import Family8Grounding.Family8LongSeparatedBufferedAdjacentFrostmanV1

/-!
# Actual normalized endpoint fields from the long-separated buffered cover

At one selected long interval, relevant Definition 2.12 data already gives
the lower C-uniformity, upper doubled-parent partitioning, and upper rescaled
Frostman certificate needed by the genuine common-fine producer.  The unified
ParameterLadder threshold supplies `4 * tau <= theta`.  This file composes
those facts and returns the literal parent-normalized adjacent upper field for
the buffered interval cover, together with the existing source field.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8RelevantDef212LongBufferedAdjacentUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CompatibleStickyScalePairCUniformFrostmanV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8Def212RescaledCWASourceFrostmanV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongSeparatedBufferedAdjacentFrostmanV1
open Family8LongSeparatedBufferedCompatiblePairV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalRelevantDef212InputsV5
open Family8ParameterLadderFourSeparationThresholdV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The actual lower endpoint cover at one sequence interval. -/
def longTauCover
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    StickyScaleCover D.family (S.tau m) :=
  C.base.cover (S.tau m) (S.delta_le_tau m)
    ((S.tau_le_theta m).trans (S.theta_le_one m))

/-- The actual upper endpoint cover at the same interval. -/
def longThetaCover
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    StickyScaleCover D.family (S.theta m) :=
  C.base.cover (S.theta m)
    ((S.delta_le_tau m).trans (S.tau_le_theta m))
    (S.theta_le_one m)

/-- The real selected-parent compatible pair at one relevant long interval.
Its upper tubes have effective radius `theta + 4*tau`. -/
noncomputable def relevantLongBufferedPair
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S P.epsilon K)
    (delta0 : NNReal)
    (hdelta : delta <= parameterLadderFourSeparatedDelta0 P delta0)
    (hFine : D.family.refinement.refined.Nonempty)
    (m : Fin depth) (hlong : S.IsLong P.epsilon m) :
    CompatibleStickyScalePair
      (longTauCover D C S m)
      (bufferedUpperScaleCover (longThetaCover D C S m) (4 * S.tau m)) :=
  longSeparatedBufferedPair hFine
    (hD.delta_pos.trans_le (S.delta_le_tau m))
    (parameterLadder_four_mul_tau_le_theta_of_isLong
      P S m hD.delta_pos hdelta hlong)
    (H.theta_doubled_parent_partitioning m hlong)

/-- Exact error produced by upper rescaled CWA, the honest upper buffer, and
lower endpoint C-uniformity. -/
def relevantLongBufferedAdjacentError
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (K : NNReal) (m : Fin depth) : ENNReal :=
  (bufferedUpperAmbientLoss (longThetaCover D C S m) (4 * S.tau m) *
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space))) *
    ((16 * (K : ENNReal)) * 16)

/-- The literal buffered interval cover has the actual Frostman error dictated
by relevant Definition 2.12 endpoint data. -/
theorem relevantLongBufferedInterval_isFrostmanAtScale
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S P.epsilon K)
    (delta0 : NNReal)
    (hdelta : delta <= parameterLadderFourSeparatedDelta0 P delta0)
    (hFine : D.family.refinement.refined.Nonempty)
    (m : Fin depth) (hlong : S.IsLong P.epsilon m)
    (htauHalf : S.tau m <= (2 : NNReal)⁻¹) :
    StickyScaleCover.IsFrostmanAtScale
      (CompatibleStickyScalePair.intervalCover
        (relevantLongBufferedPair D hD C S P H delta0 hdelta hFine m hlong))
      (relevantLongBufferedAdjacentError D C S K m) := by
  have hthetaAt := ScaleCover.isFrostmanAtScale_of_rescaledFibresCWA
    (longThetaCover D C S m)
    hD.delta_le_half (H.theta_unitRescalingGeometry m hlong)
    (H.theta_rescaled_fibres_cwa m hlong)
  simpa only [relevantLongBufferedPair,
    relevantLongBufferedAdjacentError, longTauCover, longThetaCover] using
      (longSeparated_intervalCover_isFrostmanAtScale
        (lower := longTauCover D C S m)
        (upper := longThetaCover D C S m)
        hFine (hD.delta_pos.trans_le (S.delta_le_tau m))
        (parameterLadder_four_mul_tau_le_theta_of_isLong
          P S m hD.delta_pos hdelta hlong)
        (H.theta_doubled_parent_partitioning m hlong)
        hD.delta_pos hD.delta_le_half htauHalf
        (H.tau_c_uniform m hlong) hthetaAt)

/-- The actual parent-normalized adjacent field for the buffered interval. -/
theorem relevantLongBufferedAdjacentUpper
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S P.epsilon K)
    (delta0 : NNReal)
    (hdelta : delta <= parameterLadderFourSeparatedDelta0 P delta0)
    (hFine : D.family.refinement.refined.Nonempty)
    (m : Fin depth) (hlong : S.IsLong P.epsilon m)
    (htauHalf : S.tau m <= (2 : NNReal)⁻¹)
    (herror : relevantLongBufferedAdjacentError D C S K m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        P.eta (P.N - 1))) :
    parentNormalizedFiberCFMax
        (CompatibleStickyScalePair.intervalCover
          (relevantLongBufferedPair D hD C S P H delta0 hdelta hFine m hlong)) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        P.eta (P.N - 1)) := by
  exact
    ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (CompatibleStickyScalePair.intervalCover
        (relevantLongBufferedPair D hD C S P H delta0 hdelta hFine m hlong))
      (hD.delta_pos.trans_le (S.delta_le_tau m))
      (relevantLongBufferedAdjacentError D C S K m)).mp
        (relevantLongBufferedInterval_isFrostmanAtScale
          D hD C S P H delta0 hdelta hFine m hlong htauHalf)).trans herror

/-- Both actual normalized endpoint fields at one selected long interval.
The source field is on the original `delta -> tau` cover; the adjacent field
is on the genuine `tau -> theta+4tau` buffered compatible cover. -/
theorem relevantLongBufferedNormalizedEndpointBounds
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    {K : NNReal}
    (H : RelevantFiniteSequenceDef212Inputs C S P.epsilon K)
    (delta0 : NNReal)
    (hdelta : delta <= parameterLadderFourSeparatedDelta0 P delta0)
    (hFine : D.family.refinement.refined.Nonempty)
    (m : Fin depth) (hlong : S.IsLong P.epsilon m)
    (htauHalf : S.tau m <= (2 : NNReal)⁻¹)
    (hsourceError :
      ((K : ENNReal) * 16 * volume (unitBallBody : Set Space)) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ P.eta (P.N - 1)))
    (hadjacentError : relevantLongBufferedAdjacentError D C S K m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        P.eta (P.N - 1))) :
    parentNormalizedFiberCFMax (longTauCover D C S m) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ P.eta (P.N - 1)) ∧
      parentNormalizedFiberCFMax
          (CompatibleStickyScalePair.intervalCover
            (relevantLongBufferedPair D hD C S P H delta0 hdelta hFine m hlong)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          P.eta (P.N - 1)) := by
  constructor
  · have htauAt := ScaleCover.isFrostmanAtScale_of_rescaledFibresCWA
      (longTauCover D C S m)
      hD.delta_le_half (H.tau_unitRescalingGeometry m hlong)
      (H.tau_rescaled_fibres_cwa m hlong)
    exact
      ((isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
        (longTauCover D C S m) hD.delta_pos
        ((K : ENNReal) * 16 * volume (unitBallBody : Set Space))).mp
          htauAt).trans hsourceError
  · exact relevantLongBufferedAdjacentUpper
      D hD C S P H delta0 hdelta hFine m hlong htauHalf hadjacentError

#print axioms relevantLongBufferedPair
#print axioms relevantLongBufferedInterval_isFrostmanAtScale
#print axioms relevantLongBufferedAdjacentUpper
#print axioms relevantLongBufferedNormalizedEndpointBounds

end
end Family8RelevantDef212LongBufferedAdjacentUpperV1
