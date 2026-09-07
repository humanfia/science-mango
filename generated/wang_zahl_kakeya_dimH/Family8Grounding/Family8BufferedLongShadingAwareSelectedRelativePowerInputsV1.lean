import Family8Grounding.Family8BufferedLongShadingAwareSelectedBaseDensityBundleV4
import Family8Grounding.Family8BufferedLongShadingAwareSelectedFiberFrostmanV1
import Family8Grounding.Family8ShadingAwareDensityFloorRelativePowerV4
import Mathlib.Tactic

/-!
# Same-parent relative-power inputs on the buffered long source scale

The actual mass-popular parent is retained while the universal selected-fibre
Frostman property and the density-floor power absorption are attached.  The
result contains exactly one parent and no proxy object-identification claim.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8BufferedLongShadingAwareSelectedRelativePowerInputsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open Family8ShadingAwareDensityFloorRelativePowerV4
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The same literal source parent carries the selected-fibre Frostman
certificate and both relative-power inequalities needed downstream. -/
theorem exists_bufferedLong_shadingAware_relativePowerInputs
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
    {eta p a etaF lossExp xExp baseAbsorbExp baseScaleExp : Real}
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
    let q : ENNReal := (delta : ENNReal) / (S.tau W.m : ENNReal)
    ∃ k ∈ Ppart.coarseIndices,
      IsFrostmanOn
          (((S.tau W.m / delta : NNReal) : ENNReal) ^
            P.eta (W.stage - 1))
          D.family.bodyFamily (Ppart.fiber k) (S0.coarse.tubes k).body ∧
        ((3 / 64 : ENNReal) ^ (-(2 * p + a)) *
            q ^ (-(2 * p + a)) ≤
          ((3 / 64 : ENNReal) ^ (-eta) * q ^ (-eta)) *
            ((Fintype.card {i // i ∈ S0.fiber k} : ENNReal) *
              (((3 / 64 : ENNReal) ^ (2 : Nat) * q ^ (2 : Nat)) / 2))) ∧
        q ^ (eta - (p + a)) ≤
          (stickyFiberSourceShading S0 D.shading k).shadingDensity /
            93312 / 128 := by
  dsimp only
  let S0 := longTauCover D C S W.m
  let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (hD.delta_pos.trans_le (S.delta_le_tau W.m))
    (S.delta_le_tau W.m) hactive hmass
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hdeltaOne : delta ≤ 1 := hD.delta_le_half.trans (by norm_num)
  obtain ⟨k, hk, hbase, hfloorRaw⟩ :=
    Family8BufferedLongShadingAwareSelectedBaseDensityBundleV4.BufferedNormalizedLongTerminalWitness.exists_shadingAwareSelected_baseRatio_and_densityFloor_of_powerCaps
      D hD C S P W sourceA hsourceA htauHalf hactive hmass
        hloss hX hbaseConstant hqBase hbaseGain hbaseBudget hsourceMass
  have hcover0 : stickyShadingAwareCoverLoss
      S0 D.shading (sourceA : ENNReal) ≠ 0 :=
    stickyShadingAwareCoverLoss_ne_zero S0 D.shading
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') htau hactive
  have hcoverTop : stickyShadingAwareCoverLoss
      S0 D.shading (sourceA : ENNReal) ≠ ∞ :=
    stickyShadingAwareCoverLoss_ne_top S0 D.shading
      ENNReal.coe_ne_top hmass
  have hbranch0 : (Ppart.branching : ENNReal) ≠ 0 := by
    exact_mod_cast Ppart.branching_pos.ne'
  have hbranchTop : (Ppart.branching : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  have hfloor :
      ((sourceA : ENNReal) * ((S.tau W.m : ENNReal) ^ 2 / 2)) /
          ((2 * stickyShadingAwareCoverLoss
              S0 D.shading (sourceA : ENNReal)) *
            ((2 * (Ppart.branching : ENNReal)) *
              (8 * (delta : ENNReal) ^ 2))) ≤
        (stickyFiberSourceShading S0 D.shading k).shadingDensity := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfloorRaw
  have hdensity := densityRatio_of_densityFloor_and_powerCaps
    hD.delta_pos hdeltaOne htau hcover0 hcoverTop hbranch0 hbranchTop
      hfloor hcover hbranch hdensityConstant hqDensity hdensityGain
        hdensityBudget hsourceAPower
  have hFrostmanAll :=
    Family8BufferedLongShadingAwareSelectedFiberFrostmanV1.BufferedNormalizedLongTerminalWitness.shadingAware_selectedFiber_isFrostmanOn
      D hD C S P W (sourceA : ENNReal)
        (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
        hactive hmass
  have hFrostman := hFrostmanAll k hk
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · simpa only [Ppart, S0] using hk
  · simpa only [Ppart, S0] using hFrostman
  · simpa only [S0] using hbase
  · simpa only [S0] using hdensity

#print axioms exists_bufferedLong_shadingAware_relativePowerInputs

end
end Family8BufferedLongShadingAwareSelectedRelativePowerInputsV1
