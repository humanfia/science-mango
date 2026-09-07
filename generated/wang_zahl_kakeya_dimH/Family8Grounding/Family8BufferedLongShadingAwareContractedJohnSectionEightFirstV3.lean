import Family8Grounding.Family8BufferedLongShadingAwareContractedJohnFirstEndpointV4
import Family8Grounding.Family8StickyFiberContractedJohnFirstActualVolumeEnvelopeV2
import Mathlib.Tactic

/-!
# Contracted-John first endpoint on the shading-aware buffered source scale

The parent selected by the source-mass argument is converted only to the
literal active-parent subtype required by the contracted-John construction.
The selected-fibre Frostman certificate and the final nonempty refinement are
retained on this exact same parent.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8BufferedLongShadingAwareContractedJohnSectionEightFirstV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8BufferedLongShadingAwareContractedJohnFirstEndpointV4
open Family8BufferedLongShadingAwareSelectedRelativePowerInputsV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnFirstActualVolumeEnvelopeV2
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnRelativePowerEndpointV1
open Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The actual shading-aware source parent admits a genuine nonempty
contracted-John refinement with its literal source average bounded by the
relative-power Frostman factor. -/
theorem exists_bufferedLong_shadingAware_contractedJohn_sectionEight_first
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : BufferedNormalizedLongTerminalWitness D C P S)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (htauHalf : S.tau W.m ≤ (2 : NNReal)⁻¹)
    (hactive : (longTauCover D C S W.m).activeFine.Nonempty)
    (hmass : shadingMassOn D.shading
      (longTauCover D C S W.m).activeFine ≠ 0)
    {frostmanBeta frostmanEpsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon eta delta0)
    {CKT : ENNReal} (hKT : IsKatzTao CKT D.family.bodyFamily)
    (hCKTone : 1 <= CKT) (hCKTfinite : CKT ≠ ∞)
    (hp : 0 < p) (ha : 0 < a) (hgap : 0 ≤ eta - (p + a))
    (hfrostmanBetaTwo : frostmanBeta <= 2)
    (hgammaTwo : gamma <= 2)
    (hfrostmanGammaGap : 0 <= gamma - frostmanBeta)
    (hdelta0 : contractedJohnProxyRadius delta (S.tau W.m) / 8 ≤ delta0)
    (hsmallRatio : delta / S.tau W.m ≤
      contractedJohnSourcePowerEndpointThreshold a)
    (hCratio : CKT ≤
      (((delta : ENNReal) / (S.tau W.m : ENNReal)) ^ (-p)))
    {etaF lossExp xExp baseAbsorbExp baseScaleExp : Real}
    (hloss :
      (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) ≤
        (delta : ENNReal) ^ (-lossExp))
    (hX :
      (activeCoarseCardScaleMass (longTauCover D C S W.m) : ENNReal) ≤
        (delta : ENNReal) ^ (-xExp))
    (hbaseConstant : massPopularBaseFixedConstant eta p a ≤
      (delta : ENNReal) ^ (-baseAbsorbExp))
    (hqBase : ((delta : ENNReal) / (S.tau W.m : ENNReal)) ≤
      (delta : ENNReal) ^ baseScaleExp)
    (hbaseGain : 0 ≤ eta - (2 * p + a))
    (hbaseBudget : 2 * etaF + lossExp + xExp + baseAbsorbExp ≤
      baseScaleExp * (eta - (2 * p + a)))
    (hsourceMass : (delta : ENNReal) ^ (2 * etaF) ≤
      shadingMassOn D.shading
        (longTauCover D C S W.m).activeFine)
    {densityEtaF coverExp branchExp densityAbsorbExp densityScaleExp : Real}
    (hcover : 2 * stickyShadingAwareCoverLoss
        (longTauCover D C S W.m) D.shading (sourceA : ENNReal) ≤
      (delta : ENNReal) ^ (-coverExp))
    (hbranch : 2 *
        ((shadingAwareLogPartition
          (longTauCover D C S W.m) D.shading (sourceA : ENNReal)
          (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
          (hD.delta_pos.trans_le (S.delta_le_tau W.m))
          (S.delta_le_tau W.m) hactive hmass).branching : ENNReal) ≤
      (delta : ENNReal) ^ (-branchExp))
    (hdensityConstant : (2 * 8 * 93312 * 128 : ENNReal) ≤
      (delta : ENNReal) ^ (-densityAbsorbExp))
    (hqDensity : ((delta : ENNReal) / (S.tau W.m : ENNReal)) ≤
      (delta : ENNReal) ^ densityScaleExp)
    (hdensityGain : 0 ≤ eta - (p + a) + 2)
    (hdensityBudget :
      2 * densityEtaF + coverExp + branchExp + densityAbsorbExp ≤
        densityScaleExp * (eta - (p + a) + 2))
    (hsourceAPower : (delta : ENNReal) ^ (2 * densityEtaF) ≤
      (sourceA : ENNReal)) :
    let S0 := longTauCover D C S W.m
    let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le (S.delta_le_tau W.m))
      (S.delta_le_tau W.m) hactive hmass
    ∃ kActive : {k // k ∈ S0.activeCoarse},
      kActive.1 ∈ Ppart.coarseIndices ∧
        IsFrostmanOn
          (((S.tau W.m / delta : NNReal) : ENNReal) ^
            P.eta (W.stage - 1))
          D.family.bodyFamily (Ppart.fiber kActive.1)
            (S0.coarse.tubes kActive.1).body ∧
        ∃ selected : Finset {i // i ∈ S0.fiber kActive.1},
          selected.Nonempty ∧
          (stickyFiberSourceShading S0 D.shading
              kActive.1).averageMultiplicity ≤
            contractedJohnMiddleActualFixedCoefficient
                ordinaryFiberNatCapFixedConstant
                frostmanEpsilon frostmanBeta gamma (p + a) *
              (((delta : ENNReal) / (S.tau W.m : ENNReal)) ^
                contractedJohnMiddleRatioGain
                  frostmanEpsilon frostmanBeta gamma (p + a) p) *
              sectionEightScaleCountFrostmanFactor
                delta (S.tau W.m) selected.card gamma := by
  dsimp only
  let S0 := longTauCover D C S W.m
  let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (hD.delta_pos.trans_le (S.delta_le_tau W.m))
    (S.delta_le_tau W.m) hactive hmass
  obtain ⟨kActive, hk, hFrostman, selected, hselected, havg⟩ :=
    exists_bufferedLong_shadingAware_contractedJohn_firstEndpoint
        D hD C S P W sourceA hsourceA htauHalf hactive hmass hF hKT
          hp ha hgap hdelta0 hsmallRatio hCratio
          hloss hX hbaseConstant hqBase hbaseGain hbaseBudget hsourceMass
          hcover hbranch hdensityConstant hqDensity hdensityGain
          hdensityBudget hsourceAPower
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have htauOne : S.tau W.m <= 1 := htauHalf.trans (by norm_num)
  have hsmallClosed : delta / S.tau W.m <=
      contractedJohnSourceClosedLossThreshold a :=
    hsmallRatio.trans (min_le_left _ _)
  have hscalar :=
    stickyFiberContractedJohn_selectedActualRHS_le_sectionEight
      (epsilon := frostmanEpsilon) (beta := frostmanBeta) (gamma := gamma)
      (p := p) (a := a) S0 D.shading kActive selected hselected
        hD.delta_pos hD.delta_le_half htau htauOne
        (S.delta_le_tau W.m) hCKTone hCKTfinite hKT
        hfrostmanBetaTwo hgammaTwo hfrostmanGammaGap hp ha
        hsmallClosed hCratio
  refine ⟨kActive, ?_, ?_, selected, hselected, havg.trans ?_⟩
  · simpa only [Ppart, S0] using hk
  · simpa only [Ppart, S0] using hFrostman
  · simpa only [S0] using hscalar

#print axioms
  exists_bufferedLong_shadingAware_contractedJohn_sectionEight_first

end
end Family8BufferedLongShadingAwareContractedJohnSectionEightFirstV3
