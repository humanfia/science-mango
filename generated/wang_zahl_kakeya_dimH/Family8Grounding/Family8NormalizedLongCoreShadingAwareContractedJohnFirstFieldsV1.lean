import Family8Grounding.Family8NormalizedLongCoreShadingAwareContractedJohnSameParentFirstBundleV1
import Mathlib.Tactic

/-!
# Long-core first fields from the same-parent source bundle

The finite shading-selector loss belongs to `firstLoss`, not to an unrelated
middle count.  This successor packages that exact multiplication while
retaining the same source parent and the same contracted-John selected set.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongCoreShadingAwareContractedJohnFirstFieldsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BufferedLongShadingAwareSelectedRelativePowerInputsV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8NormalizedLongCoreShadingAwareContractedJohnSameParentFirstBundleV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The actual first average and first loss for the long-core record. -/
theorem exists_normalizedLongCore_shadingAware_contractedJohn_firstFields
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (htauHalf : S.tau W.m ≤ (2 : NNReal)⁻¹)
    (hactive : (longTauCover D C S W.m).activeFine.Nonempty)
    (hmass : shadingMassOn D.shading
      (longTauCover D C S W.m).activeFine ≠ 0)
    {frostmanBeta frostmanEpsilon eta p a : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters
      frostmanBeta frostmanEpsilon eta delta0)
    {CKT : ENNReal} (hKT : IsKatzTao CKT D.family.bodyFamily)
    (hCKTone : 1 ≤ CKT) (hCKTfinite : CKT ≠ ∞)
    (hp : 0 < p) (ha : 0 < a) (hgap : 0 ≤ eta - (p + a))
    (hfrostmanBetaTwo : frostmanBeta ≤ 2)
    (hgammaTwo : gamma ≤ 2)
    (hfrostmanGammaGap : 0 ≤ gamma - frostmanBeta)
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
    let selectedParents := shadingAwareSelectedParents
      S0 D.shading (sourceA : ENNReal)
        (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
        (hD.delta_pos.trans_le (S.delta_le_tau W.m)) hactive hmass
    let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
    let selectorLoss : ENNReal :=
      (retention : ENNReal) * (selectedParents.card : ENNReal)
    let rawFirstLoss : ENNReal :=
      contractedJohnMiddleActualFixedCoefficient
          ordinaryFiberNatCapFixedConstant
          frostmanEpsilon frostmanBeta gamma (p + a) *
        (((delta : ENNReal) / (S.tau W.m : ENNReal)) ^
          contractedJohnMiddleRatioGain
            frostmanEpsilon frostmanBeta gamma (p + a) p)
    let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le (S.delta_le_tau W.m))
      (S.delta_le_tau W.m) hactive hmass
    ∃ kActive : {k // k ∈ S0.activeCoarse},
      kActive.1 ∈ Ppart.coarseIndices ∧
        ∃ selected : Finset {i // i ∈ S0.fiber kActive.1},
          selected.Nonempty ∧
          let firstAverage := selectorLoss *
            (stickyFiberSourceShading S0 D.shading
              kActive.1).averageMultiplicity
          let firstLoss := selectorLoss * rawFirstLoss
          (activeFineShading S0 D.shading).averageMultiplicity ≤
              firstAverage ∧
            firstAverage ≤ firstLoss *
              sectionEightScaleCountFrostmanFactor
                delta (S.tau W.m) selected.card gamma := by
  dsimp only
  let S0 := longTauCover D C S W.m
  let selectedParents := shadingAwareSelectedParents
    S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le (S.delta_le_tau W.m)) hactive hmass
  let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
  let selectorLoss : ENNReal :=
    (retention : ENNReal) * (selectedParents.card : ENNReal)
  let rawFirstLoss : ENNReal :=
    contractedJohnMiddleActualFixedCoefficient
        ordinaryFiberNatCapFixedConstant
        frostmanEpsilon frostmanBeta gamma (p + a) *
      (((delta : ENNReal) / (S.tau W.m : ENNReal)) ^
        contractedJohnMiddleRatioGain
          frostmanEpsilon frostmanBeta gamma (p + a) p)
  let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (hD.delta_pos.trans_le (S.delta_le_tau W.m))
    (S.delta_le_tau W.m) hactive hmass
  obtain ⟨kActive, hk, hsource, selected, hselected, hfirst⟩ :=
    exists_normalizedLongCore_shadingAware_sameParent_sectionEight_firstBundle
      D hD C S P W sourceA hsourceA htauHalf hactive hmass hF hKT
        hCKTone hCKTfinite hp ha hgap hfrostmanBetaTwo hgammaTwo
        hfrostmanGammaGap hdelta0 hsmallRatio hCratio
        hloss hX hbaseConstant hqBase hbaseGain hbaseBudget hsourceMass
        hcover hbranch hdensityConstant hqDensity hdensityGain
        hdensityBudget hsourceAPower
  refine ⟨kActive, ?_, selected, hselected, ?_, ?_⟩
  · simpa only [Ppart, S0] using hk
  · simpa only [selectorLoss, retention, selectedParents, S0] using hsource
  · calc
      selectorLoss *
          (stickyFiberSourceShading S0 D.shading
            kActive.1).averageMultiplicity ≤
        selectorLoss *
          (rawFirstLoss * sectionEightScaleCountFrostmanFactor
            delta (S.tau W.m) selected.card gamma) :=
        mul_le_mul' le_rfl (by
          simpa only [rawFirstLoss, S0, mul_assoc] using hfirst)
      _ = (selectorLoss * rawFirstLoss) *
          sectionEightScaleCountFrostmanFactor
            delta (S.tau W.m) selected.card gamma := by
        ac_rfl

#print axioms
  exists_normalizedLongCore_shadingAware_contractedJohn_firstFields

end
end Family8NormalizedLongCoreShadingAwareContractedJohnFirstFieldsV1
