import Family8Grounding.Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedGlobalFirstFactorEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8FullRefinementActualDatumV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8AllFrostmanStickyUnionProducerV1
open Family8ContractedJohnActualTubeProxyV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyBoundedFiberPartitionCoreV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8CanonicalBufferedGlobalKatzTaoBoundedFrozenAssemblyV1.Witness
open Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1.Witness
open Family8CanonicalBufferedGlobalRelativeScaleGainV1.Witness
open Family8StickyMassPopularFixedKatzTaoCoefficientV1
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyBoundedFiberFactorizationRoundTripV2
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Canonical global first-factor endpoint

This is the same-object composition omitted by the lower-level modules.  It
uses the literal bounded partition and frozen assembly returned by the global
cover.  The source floor has no tau-active cardinality divisor.  All finite
constants, the frozen logarithm, the `X <= 1024 C_KT` cap, and the two
contracted-John scale requirements are absorbed by one explicit threshold.
-/

/-- Pulling a positive target scale back through the gain `delta^s`. -/
def positivePowerPullbackThreshold (s : Real) (target : NNReal) : NNReal :=
  target ^ (1 / s)

theorem positivePowerPullbackThreshold_pos
    {s : Real} {target : NNReal} ( _hs : 0 < s) (htarget : 0 < target) :
    0 < positivePowerPullbackThreshold s target := by
  exact NNReal.rpow_pos htarget

theorem rpow_le_target_of_le_positivePowerPullbackThreshold
    {delta target : NNReal} {s : Real} (hs : 0 < s)
    (hsmall : delta <= positivePowerPullbackThreshold s target) :
    delta ^ s <= target := by
  calc
    delta ^ s <= (target ^ (1 / s)) ^ s :=
      NNReal.rpow_le_rpow hsmall hs.le
    _ = target := by
      rw [← NNReal.rpow_mul]
      convert NNReal.rpow_one target using 1
      field_simp [ne_of_gt hs]

/-- The single small-delta threshold for the canonical first factor. -/
def canonicalBufferedGlobalFirstFactorThreshold
    (stoppingEpsilon etaOuter p a xAbs lossExp constAbsorb : Real)
    (delta0 : NNReal) : NNReal :=
  min (canonicalGlobalXPowerThreshold xAbs)
    (min (activeFrozenComparableLossAbsorptionThreshold lossExp)
      (min (massPopularDensityPowerThreshold constAbsorb)
        (min (massPopularBasePowerThreshold etaOuter p a constAbsorb)
          (positivePowerPullbackThreshold (stoppingEpsilon ^ 2)
            (min (contractedJohnSourcePowerEndpointThreshold a) delta0)))))

theorem canonicalBufferedGlobalFirstFactorThreshold_pos
    {stoppingEpsilon etaOuter p a xAbs lossExp constAbsorb : Real}
    {delta0 : NNReal} (hepsilon : 0 < stoppingEpsilon)
    (hdelta0 : 0 < delta0) :
    0 < canonicalBufferedGlobalFirstFactorThreshold stoppingEpsilon
      etaOuter p a xAbs lossExp constAbsorb delta0 := by
  apply lt_min
  · exact canonicalGlobalXPowerThreshold_pos xAbs
  apply lt_min
  · exact activeFrozenComparableLossAbsorptionThreshold_pos lossExp
  apply lt_min
  · exact finiteConstantSmallDeltaThreshold_pos _ _
  apply lt_min
  · exact finiteConstantSmallDeltaThreshold_pos _ _
  · apply positivePowerPullbackThreshold_pos
    · positivity
    · exact lt_min (contractedJohnSourcePowerEndpointThreshold_pos a) hdelta0

/-- The long-interval gain itself supplies the fixed-Katz--Tao power premise.
The only exponent bookkeeping is `etaKT <= scaleExp * p`. -/
theorem katzTaoConstant_le_ratio_negativePower_of_globalGain
    {delta : NNReal} {q C : ENNReal} {etaKT scaleExp p : Real}
    (hdeltaOne : delta <= 1) (hp : 0 < p)
    (hCKT : C <= (delta : ENNReal) ^ (-etaKT))
    (hq : q <= (delta : ENNReal) ^ scaleExp)
    (hparameter : etaKT <= scaleExp * p) :
    C <= q ^ (-p) := by
  have hdOne : (delta : ENNReal) <= 1 := by exact_mod_cast hdeltaOne
  have hqPower : q ^ p <=
      ((delta : ENNReal) ^ scaleExp) ^ p :=
    ENNReal.rpow_le_rpow hq hp.le
  calc
    C <= (delta : ENNReal) ^ (-etaKT) := hCKT
    _ <= (delta : ENNReal) ^ (-(scaleExp * p)) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hdOne
      linarith
    _ = (((delta : ENNReal) ^ scaleExp) ^ p)⁻¹ := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_mul]
    _ <= (q ^ p)⁻¹ := ENNReal.inv_le_inv' hqPower
    _ = q ^ (-p) := by rw [ENNReal.rpow_neg]

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real} {etaSeq : Nat -> Real}

theorem exists_canonicalBufferedGlobal_firstFactor_relativePower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti N stoppingEpsilon etaSeq Sseq)
    (hepsilon : 0 < stoppingEpsilon)
    (hepsilonHalf : stoppingEpsilon <= 1 / 2)
    (hbufferedSixteenth :
      canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {etaF beta frostmanEpsilon etaOuter p a etaKT xAbs lossExp
      constAbsorb : Real}
    {delta0 : NNReal}
    (hFsource : FrostmanHypotheses D etaF)
    (hF : FrostmanAtParameters beta frostmanEpsilon etaOuter delta0)
    {CKT : ENNReal} (hCKTone : 1 <= CKT) (hCKTfinite : CKT ≠ ∞)
    (hKTsource : IsKatzTao CKT D.family.bodyFamily)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (hp : 0 < p) (ha : 0 < a)
    (hxAbs : 0 < xAbs) (hlossExp : 0 < lossExp)
    (hconstAbsorb : 0 < constAbsorb)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hCKTRatioBudget : etaKT <= stoppingEpsilon ^ 2 * p)
    (hgain : 0 <= etaOuter - (2 * p + a))
    (hpowerBudget :
      2 * etaF + lossExp + (etaKT + xAbs) + constAbsorb <=
        stoppingEpsilon ^ 2 * (etaOuter - (2 * p + a)))
    (hsmall : delta <=
      canonicalBufferedGlobalFirstFactorThreshold stoppingEpsilon
        etaOuter p a xAbs lossExp constAbsorb delta0) :
    let E := fullRefinementDatum D
    let G := canonicalBufferedGlobalCover W hD.delta_pos
      hepsilon.le hepsilonHalf
    let U := activeFineRestrictedScaleCover G
    let Y := activeFineRestrictedShading G E.shading
    let M := katzTaoDoubledFiberNatCap delta
      (canonicalBufferedRadius W) CKT
    let hsource0 :
        (IndexedShadingRefinement.restrictTo E.shading
          G.activeFine).shading.shadingMass ≠ 0 := by
      have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
          D.shading.shadingMass :=
        delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
      have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
        ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
      have hmass : E.shading.shadingMass ≠ 0 := by
        rw [fullRefinementDatum_shadingMass]
        exact ne_of_gt (hpositive.trans_le hfloor)
      have hactive : G.activeFine = Finset.univ := by
        rw [G.activeFine_eq_refined, fullRefinementDatum_refined]
      rw [hactive, restrictTo_univ_shadingMass]
      exact hmass
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      activeFineRestrictedSourceMass_ne_zero G E.shading hsource0
    let hM : forall k, k ∈ U.activeCoarse → (U.fiber k).card <= M :=
      activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
        G hD.delta_pos hD.delta_le_half
          (canonicalBufferedRadius_le_one W hD.delta_pos
            hepsilon.le hepsilonHalf)
          hCKTfinite hKTsource
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      ((Sseq.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon.le))
      hcoarse M hM
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ G.activeFine}
          (Fin U.coarseCard) ∧
      (delta : ENNReal) ^ (2 * etaF) <=
        (sourceActiveFineShading
          Pcoarse.asConvexFactorization Y).shadingMass ∧
      ∃ q : {q // q ∈
          (selectedFineScaleCover U A.refinement.indices
            (assembly_indices_subset_activeFine U Y 1 A)).activeCoarse},
        ∃ selected : Finset {i // i ∈
            (selectedFineScaleCover U A.refinement.indices
              (assembly_indices_subset_activeFine U Y 1 A)).fiber q.1},
          selected.Nonempty ∧
          (actualRefinementShading A).averageMultiplicity <=
            4 * (A.frozenCoarse.averageMultiplicity *
              (stickyFiberContractedJohnSourceClosedLoss CKT *
                frostmanMultiplicityRHS
                  (contractedJohnProxyRadius delta
                    (canonicalBufferedRadius W) / 8)
                  (restrictActualTubeDatum
                    (eighthNormalizedDatum
                      (stickyFiberContractedJohnProxyDatum
                        (selectedFineScaleCover U A.refinement.indices
                          (assembly_indices_subset_activeFine U Y 1 A))
                        (selectedFineShading U A.refinement.indices
                          A.refinement.shading)
                        (canonicalBufferedRadius_pos W hD.delta_pos
                          hepsilon.le)
                        (canonicalBufferedRadius_le_one W hD.delta_pos
                          hepsilon.le hepsilonHalf) q)) selected).actualFamilyVolume
                  frostmanEpsilon beta)) := by
  dsimp only
  let E := fullRefinementDatum D
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilon.le hepsilonHalf
  let U := activeFineRestrictedScaleCover G
  let Y := activeFineRestrictedShading G E.shading
  let b := canonicalBufferedRadius W
  let M := katzTaoDoubledFiberNatCap delta b CKT
  have hbpos : 0 < b := canonicalBufferedRadius_pos W hD.delta_pos hepsilon.le
  have hbOne : b <= 1 :=
    canonicalBufferedRadius_le_one W hD.delta_pos hepsilon.le hepsilonHalf
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hbHalf : b <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenHalf
  have hdeltaOne : delta <= 1 := by
    exact hD.delta_le_half.trans (by norm_num)
  have hscale : delta <= b :=
    (Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon.le)
  have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
      D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
  have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
  have hactive : G.activeFine = Finset.univ := by
    rw [G.activeFine_eq_refined, fullRefinementDatum_refined]
  have hsource0 :
      (IndexedShadingRefinement.restrictTo E.shading
        G.activeFine).shading.shadingMass ≠ 0 := by
    rw [hactive, restrictTo_univ_shadingMass,
      fullRefinementDatum_shadingMass]
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero G E.shading hsource0
  have hKTfull : IsKatzTao CKT E.family.bodyFamily := hKTsource
  have hKTU : IsKatzTao CKT
      (activeFineRestrictedFamily G).bodyFamily :=
    activeFineRestrictedFamily_isKatzTao G hKTfull
  have hM : forall k, k ∈ U.activeCoarse → (U.fiber k).card <= M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      G hD.delta_pos hD.delta_le_half hbOne hCKTfinite hKTfull
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U hscale hcoarse M hM
  obtain ⟨A, hAloss, hsourceFloor, _hmass, _hdensity, _hproduct⟩ :=
    exists_fullRefinement_canonicalBufferedGlobal_boundedFrozenAssembly
      D hD Cmulti Sseq W hepsilon.le hepsilonHalf hFsource
        hCKTfinite hKTsource
  refine ⟨A, hAloss, hsourceFloor, ?_⟩
  have hsmallX : delta <= canonicalGlobalXPowerThreshold xAbs :=
    hsmall.trans (min_le_left _ _)
  have hsmallLog : delta <=
      activeFrozenComparableLossAbsorptionThreshold lossExp :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallDensity : delta <=
      massPopularDensityPowerThreshold constAbsorb :=
    hsmall.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallBase : delta <=
      massPopularBasePowerThreshold etaOuter p a constAbsorb :=
    hsmall.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
  have hsmallRelative : delta <=
      positivePowerPullbackThreshold (stoppingEpsilon ^ 2)
        (min (contractedJohnSourcePowerEndpointThreshold a) delta0) :=
    hsmall.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (le_refl _)))))
  have hdeltaPower : delta ^ (stoppingEpsilon ^ 2) <=
      min (contractedJohnSourcePowerEndpointThreshold a) delta0 :=
    rpow_le_target_of_le_positivePowerPullbackThreshold
      (by positivity) hsmallRelative
  have hqNN : delta / b <= delta ^ (stoppingEpsilon ^ 2) :=
    delta_div_canonicalBufferedRadius_le_rpow_sq
      W hD.delta_pos hepsilon.le
  have hqSmall : delta / b <=
      min (contractedJohnSourcePowerEndpointThreshold a) delta0 :=
    hqNN.trans hdeltaPower
  have hsmallRatio : delta / b <=
      contractedJohnSourcePowerEndpointThreshold a :=
    hqSmall.trans (min_le_left _ _)
  have hqDelta0 : delta / b <= delta0 :=
    hqSmall.trans (min_le_right _ _)
  have hproxyDelta0 : contractedJohnProxyRadius delta b / 8 <= delta0 := by
    calc
      contractedJohnProxyRadius delta b / 8 =
          (3 / 64 : NNReal) * (delta / b) :=
        contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hbpos
      _ <= 1 * (delta / b) := by
        gcongr
        change (3 : Real) / 64 <= 1
        norm_num
      _ = delta / b := one_mul _
      _ <= delta0 := hqDelta0
  obtain ⟨hq0, hqTop, hqPower⟩ :=
    canonicalBufferedGlobal_ratio_power_inputs
      D hD Cmulti Sseq W hepsilon.le
  have hCratio : CKT <=
      (((delta : ENNReal) / (b : ENNReal)) ^ (-p)) :=
    katzTaoConstant_le_ratio_negativePower_of_globalGain
      hdeltaOne hp hCKT hqPower hCKTRatioBudget
  have hX : (activeCoarseCardScaleMass U : ENNReal) <=
      (delta : ENNReal) ^ (-(etaKT + xAbs)) :=
    canonicalBufferedGlobal_restricted_cardScaleMass_le_power
      D hD Cmulti Sseq W hepsilon.le hepsilonHalf hbHalf hKTEvery
        hxAbs hCKT hsmallX
  have hlogRaw := canonicalBufferedGlobal_frozenLoss_le_power
    D hD Cmulti Sseq W hepsilon.le hepsilonHalf
      hlossExp hsmallLog
  have hAlossPower : (A.loss : ENNReal) <=
      (delta : ENNReal) ^ (-lossExp) := by
    rw [hAloss]
    exact hlogRaw
  have hdensityConstant := massPopularDensityFixedConstant_le_power
    hconstAbsorb hD.delta_pos hsmallDensity
  have hbaseConstant := massPopularBaseFixedConstant_le_power
    hconstAbsorb hD.delta_pos hsmallBase
  have hfactor : Pcoarse.asConvexFactorization =
      toConvexFactorization U :=
    boundedFiber_asConvexFactorization_eq_toConvexFactorization
      U hscale hcoarse M hM
  have hsourceFloorCanonical : (delta : ENNReal) ^ (2 * etaF) <=
      (sourceActiveFineShading (toConvexFactorization U) Y).shadingMass := by
    rw [<- hfactor]
    exact hsourceFloor
  have hdensityEnvelope := densityEnvelope_of_powerCaps
    hD.delta_pos hdeltaOne hq0 hqTop hCratio
      (le_refl _) (le_refl _) hdensityConstant hqPower hgain
        hpowerBudget hsourceFloorCanonical
  have hbaseEnvelope := baseEnvelope_of_powerCaps
    hD.delta_pos hdeltaOne hq0 hqTop
      (le_refl _) (le_refl _) hbaseConstant hqPower hgain
        hpowerBudget hsourceFloorCanonical
  have hgap : 0 <= etaOuter - (p + a) := by linarith
  exact exists_boundedAssembly_massPopular_relativePower_factorized_of_fixedKatzTaoEnvelope
    hF U Y 1 hscale hcoarse hM A hD.delta_pos hD.delta_le_half
      hbpos hbOne hscale hKTU hCKTone hCKTfinite hp ha hgap
      hproxyDelta0 hsmallRatio hCratio hsource hAlossPower hX
      hdensityEnvelope hbaseEnvelope

#print axioms positivePowerPullbackThreshold_pos
#print axioms rpow_le_target_of_le_positivePowerPullbackThreshold
#print axioms canonicalBufferedGlobalFirstFactorThreshold_pos
#print axioms katzTaoConstant_le_ratio_negativePower_of_globalGain
#print axioms exists_canonicalBufferedGlobal_firstFactor_relativePower

end Witness
end
end Family8CanonicalBufferedGlobalFirstFactorEndpointV1
