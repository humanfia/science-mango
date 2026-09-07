import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import Family8Grounding.Family8BufferedLongShadingAwareContractedJohnSectionEightFirstV3
import Family8Grounding.Family8StickyShadingAwareSelectedBaseRatioMassV1
import Family8Grounding.Family8StickyWholeFiberMassAverageTransportV1
import Mathlib.Tactic

/-!
# Same-parent mass retention and Section 8 first factor

The maximum-mass parent is selected exactly once.  That same literal parent
carries source-to-fibre average retention,
the relative-power contracted-John input, and the final Section 8 first-factor
bound.  No two existential parent witnesses are identified after the fact.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongCoreShadingAwareContractedJohnSameParentFirstBundleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BufferedNormalizedLongTerminalWitnessV1
open Family8BufferedLongShadingAwareSelectedRelativePowerInputsV1
open Family8BufferedLongShadingAwareSelectedFiberDensityFloorV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8RelevantDef212LongBufferedAdjacentUpperV1
open Family8ShadingAwareDensityFloorRelativePowerV4
open Family8StickyFiberContractedJohnFirstActualVolumeEnvelopeV2
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnRelativePowerEndpointV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareSelectedBaseRatioMassV1
open Family8StickyShadingAwareSelectedFiberDensityFloorV1
open Family8StickyWholeFiberMassAverageTransportV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- One actual source parent supplies both the active-source retention factor
and the literal Section 8 first-factor estimate. -/
theorem exists_normalizedLongCore_shadingAware_sameParent_sectionEight_firstBundle
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
    let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le (S.delta_le_tau W.m))
      (S.delta_le_tau W.m) hactive hmass
    ∃ kActive : {k // k ∈ S0.activeCoarse},
      kActive.1 ∈ Ppart.coarseIndices ∧
        (activeFineShading S0 D.shading).averageMultiplicity ≤
          ((retention : ENNReal) * (selectedParents.card : ENNReal)) *
            (stickyFiberSourceShading S0 D.shading
              kActive.1).averageMultiplicity ∧
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
  let selectedParents := shadingAwareSelectedParents
    S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le (S.delta_le_tau W.m)) hactive hmass
  let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
  let Ppart := shadingAwareLogPartition S0 D.shading (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (hD.delta_pos.trans_le (S.delta_le_tau W.m))
    (S.delta_le_tau W.m) hactive hmass
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have htauOne : S.tau W.m ≤ 1 := htauHalf.trans (by norm_num)
  obtain ⟨k, hkSelected, hstrong, hbase⟩ :=
    exists_shadingAwareSelected_massPopular_baseRatio_and_mass_of_powerCaps
      S0 D.shading (sourceA : ENNReal)
        (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
        hD.delta_pos hD.delta_le_half htau hactive hmass
        hloss hX hbaseConstant hqBase hbaseGain hbaseBudget hsourceMass
  have hkPpart : k ∈ Ppart.coarseIndices := by
    simpa only [Ppart, S0, shadingAwareLogPartition_coarseIndices] using
      hkSelected
  have hkActive : k ∈ S0.activeCoarse :=
    shadingAwareSelectedParents_subset_activeCoarse
      S0 D.shading (sourceA : ENNReal)
        (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
        htau hactive hmass hkSelected
  let kActive : {k // k ∈ S0.activeCoarse} := ⟨k, hkActive⟩
  have hactiveAverage :
      (activeFineShading S0 D.shading).averageMultiplicity ≤
        ((retention : ENNReal) * (selectedParents.card : ENNReal)) *
          (stickyFiberSourceShading S0 D.shading k).averageMultiplicity := by
    apply activeFine_averageMultiplicity_le_mul_stickyFiber_of_mass
    simpa only [retention, selectedParents, S0, mul_assoc] using hstrong
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
  have hfloorRaw := shadingAwareSelectedParent_density_floor
    S0 D.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      htau htauHalf hactive hmass hD.delta_le_half k hkSelected
  have hfloor :
      ((sourceA : ENNReal) * ((S.tau W.m : ENNReal) ^ 2 / 2)) /
          ((2 * stickyShadingAwareCoverLoss
              S0 D.shading (sourceA : ENNReal)) *
            ((2 * (Ppart.branching : ENNReal)) *
              (8 * (delta : ENNReal) ^ 2))) ≤
        (stickyFiberSourceShading S0 D.shading k).shadingDensity := by
    simpa only [Ppart, S0, shadingAwareLogPartition_branching,
      Nat.cast_mul, Nat.cast_ofNat] using hfloorRaw
  have hdensity := densityRatio_of_densityFloor_and_powerCaps
    hD.delta_pos (hD.delta_le_half.trans (by norm_num)) htau
      hcover0 hcoverTop hbranch0 hbranchTop hfloor hcover hbranch
        hdensityConstant hqDensity hdensityGain hdensityBudget hsourceAPower
  obtain ⟨selected, hselected, havgRaw⟩ :=
    exists_stickyFiberContractedJohn_global_average_le_relativePower_frostmanRHS
      hF S0 D.shading hD.delta_pos hD.delta_le_half htau htauOne
        (S.delta_le_tau W.m) kActive hKT hp ha hgap hdelta0 hsmallRatio
          hCratio
          (by simpa only [S0, kActive] using hdensity)
          (by simpa only [S0, kActive] using hbase)
  have hsmallClosed : delta / S.tau W.m ≤
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
  refine ⟨kActive, ?_, ?_, selected, hselected, havgRaw.trans ?_⟩
  · simpa only [Ppart, S0] using hkPpart
  · simpa only [S0, kActive] using hactiveAverage
  · simpa only [S0] using hscalar

#print axioms
  exists_normalizedLongCore_shadingAware_sameParent_sectionEight_firstBundle

end
end Family8NormalizedLongCoreShadingAwareContractedJohnSameParentFirstBundleV1
