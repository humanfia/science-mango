import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveBoundedFrozenAssemblyV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveBoundedSourceFloorV5
import Family8Grounding.Family8NormalizedLongCoreTauActiveFrozenOuterGammaThirdFactorFixedConflictV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveFrozenOuterThirdScalarPowerV1
import Mathlib.Tactic

/-!
# Same-object frozen third bundle from a normalized long core

The bounded partition, frozen assembly, surviving final fibre, and Section-8
third-factor estimate are constructed on one literal dependent object.  All
assembly-dependent scalar inputs of the frozen-outer endpoint are discharged
from the actual logarithmic loss, Katz--Tao fibre cap, conflict cap, source
mass floor, and long-buffered base envelope.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreTauActiveSameObjectGammaThirdBundleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveBoundedFrozenAssemblyV2
open Family8NormalizedLongCoreTauActiveBoundedSourceFloorV5
open Family8NormalizedLongCoreTauActiveFrozenOuterGammaThirdFactorFixedConflictV1
open Family8NormalizedLongCoreTauActiveFrozenOuterThirdScalarPowerV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyParentHullVolumeBoundV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The normalized long core produces one master frozen assembly carrying its
literal final-fibre witness and the official frozen third-factor bundle. -/
theorem exists_fullRefinement_coreNativeTauActive_sameObject_gammaThirdBundle
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {etaSource etaKTSource etaThird epsilonThird etaKT lossEta
      fiberAbsorbEta conflictAbsorbEta baseAbsorbEta : Real}
    {delta0 : NNReal}
    (hFsource : FrostmanHypotheses D etaSource)
    (hKTsource : KatzTaoHypotheses D etaKTSource)
    (hFthird : FrostmanAtParameters gamma epsilonThird etaThird delta0)
    (hbeta : 0 < beta) (hgammaTwo : gamma <= 2)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hCKTone : 1 <= CKT)
    (hKTEvery : C.base.IsKatzTaoAtEveryScale CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hlossEta : 0 < lossEta)
    (hfiberAbsorbEta : 0 < fiberAbsorbEta)
    (hconflictAbsorbEta : 0 < conflictAbsorbEta)
    (hbaseAbsorbEta : 0 < baseAbsorbEta)
    (hdeltaLog : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta)
    (hdeltaFiber : delta <=
      Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberNatCapSmallDeltaThreshold
        fiberAbsorbEta)
    (hdeltaConflict : delta <=
      Family8FrozenOuterThirdKatzTaoDensityPowerEnvelopeV3.frozenOuterThirdKatzTaoDensitySmallDeltaThreshold
        conflictAbsorbEta)
    (hdeltaBase : delta <=
      frozenOuterThirdKatzTaoBaseSmallDeltaThreshold baseAbsorbEta)
    (hdelta0 : canonicalBufferedRadius W / 8 <= delta0)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hetaThird : 0 <= etaThird)
    (hbaseScaleGain : 0 <=
      (1 - P.epsilon) * etaThird -
        (10 * P.eta W.stage / (P.epsilon * beta)))
    (hbaseBudget : 2 * etaKT + baseAbsorbEta <=
      P.epsilon *
        ((1 - P.epsilon) * etaThird -
          (10 * P.eta W.stage / (P.epsilon * beta))))
    (hdensityPowerBudget :
      (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ etaThird) *
          (delta : ENNReal) ^
            (-(lossEta +
              Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberPowerEnvelope
                P.epsilon etaKT fiberAbsorbEta +
              (2 * etaKT + conflictAbsorbEta))) <=
        (delta : ENNReal) ^ (2 * etaSource) /
          (katzTaoDoubledFiberNatCap
            delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal)) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let M := katzTaoDoubledFiberNatCap
      (S.tau W.m) (canonicalBufferedRadius W) CKT
    let hsource0 :
        (IndexedShadingRefinement.restrictTo Dtau.shading
          U0.activeFine).shading.shadingMass ≠ 0 := by
      have hsourceTau :
          (IndexedShadingRefinement.restrictTo E.shading
            (tauScaleCover E C S W).activeFine).shading.shadingMass ≠ 0 := by
        rw [(tauScaleCover E C S W).activeFine_eq_refined]
        exact fullRefinementDatum_restricted_shadingMass_ne_zero_of_frostman
          D hD hFsource
      exact canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        E hE C S P W hepsilonHalf hsourceTau
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      activeFineRestrictedSourceMass_ne_zero U0 Dtau.shading hsource0
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
      activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
        U0
          (hD.delta_pos.trans_le (S.delta_le_tau W.m))
          ((tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
            (hbufferedSixteenth.trans (by
              change (1 : Real) / 16 <= (2 : Real)⁻¹
              norm_num)))
          (hbufferedSixteenth.trans (by
            change (1 : Real) / 16 <= (1 : Real)
            norm_num))
          hCKTfinite
          (tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
            E C S P W
              (hKTEvery (S.tau W.m)
                (S.delta_le_tau W.m)
                ((S.tau_le_theta W.m).trans (S.theta_le_one W.m))))
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse M hM
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) /\
      exists k, k ∈ Pcoarse.coarseIndices /\
        0 < volume (finalFiberShading A k).shadedUnion /\
        Nonempty (CoreNativeFrozenThirdBundle Pcoarse.asConvexFactorization Y A
          (canonicalBufferedRadius W)
          (eighthSelectedThirdFactorLoss
            (canonicalBufferedRadius W)
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal) epsilonThird gamma)
          gamma) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  let M := katzTaoDoubledFiberNatCap
    (S.tau W.m) (canonicalBufferedRadius W) CKT
  have hsourceTau :
      (IndexedShadingRefinement.restrictTo E.shading
        (tauScaleCover E C S W).activeFine).shading.shadingMass ≠ 0 := by
    rw [(tauScaleCover E C S W).activeFine_eq_refined]
    exact fullRefinementDatum_restricted_shadingMass_ne_zero_of_frostman
      D hD hFsource
  have hsource0 :
      (IndexedShadingRefinement.restrictTo Dtau.shading
        U0.activeFine).shading.shadingMass ≠ 0 :=
    canonicalBufferedTauActiveCover_restrictedMass_ne_zero
      E hE C S P W hepsilonHalf hsourceTau
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero U0 Dtau.shading hsource0
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ :=
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
      (hbufferedSixteenth.trans (by
        change (1 : Real) / 16 <= (2 : Real)⁻¹
        norm_num))
  have hbOne : canonicalBufferedRadius W <= 1 :=
    hbufferedSixteenth.trans (by
      change (1 : Real) / 16 <= (1 : Real)
      norm_num)
  have hKTtau : IsKatzTao CKT Dtau.family.bodyFamily :=
    tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
      E C S P W
        (hKTEvery (S.tau W.m) (S.delta_le_tau W.m)
          ((S.tau_le_theta W.m).trans (S.theta_le_one W.m)))
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      U0 (hD.delta_pos.trans_le (S.delta_le_tau W.m))
        htauHalf hbOne hCKTfinite hKTtau
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
    hcoarse M hM
  obtain ⟨A, hAloss, k, hk, hkpositive⟩ :=
    exists_fullRefinement_canonicalBufferedTauActive_boundedFrozenAssembly
      D hD C S P W hepsilonHalf hbufferedSixteenth
        hFsource hCKTfinite hKTEvery
  have hsourceLower :
      (delta : ENNReal) ^ (2 * etaSource) /
          (katzTaoDoubledFiberNatCap
            delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) <=
        (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass :=
    fullRefinement_canonicalBufferedTauActive_bounded_sourceMass_lower_exactCap
      D hD C S P W hepsilonHalf hbufferedSixteenth
        hFsource hKTsource hCKTfinite hKTEvery
  have hsourceP0 :
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass ≠ 0 := by
    have hfloorPos : 0 <
        (delta : ENNReal) ^ (2 * etaSource) /
          (katzTaoDoubledFiberNatCap
            delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) := by
      exact ENNReal.div_pos
        (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
          ENNReal.coe_ne_top).ne'
        ENNReal.coe_ne_top
    exact ne_of_gt (hfloorPos.trans_le hsourceLower)
  have hbranchingLoss : Pcoarse.branchingLoss = M := by rfl
  have hbranching : Pcoarse.branching = 1 := by rfl
  have hdensityRaw :=
    canonicalBufferedTauActive_frozenOuterThirdScalar_le_power
      E hE C S P W hepsilonHalf hCKTfinite hCKTone hCKT
        hlossEta hfiberAbsorbEta hconflictAbsorbEta
        hdeltaLog hdeltaFiber hdeltaConflict Pcoarse hbranchingLoss
        hbranching Y A hAloss
  have hdensityScalar :
      ((((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ etaThird *
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
            (8 * (1024 * CKT))) <=
        (delta : ENNReal) ^ (2 * etaSource) /
          (katzTaoDoubledFiberNatCap
            delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) := by
    calc
      ((((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ etaThird *
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
            (8 * (1024 * CKT))) =
          (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ etaThird) *
            ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                ENNReal) * 128) *
              (((A.loss : ENNReal) *
                  ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
                (8 * (1024 * CKT)))) := by ring
      _ <= (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ etaThird) *
          (delta : ENNReal) ^
            (-(lossEta +
              Family8LongIntervalOrdinaryFiberCapNumericsV1.ordinaryFiberPowerEnvelope
                P.epsilon etaKT fiberAbsorbEta +
              (2 * etaKT + conflictAbsorbEta))) :=
        mul_le_mul' le_rfl hdensityRaw
      _ <= (delta : ENNReal) ^ (2 * etaSource) /
          (katzTaoDoubledFiberNatCap
            delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) :=
        hdensityPowerBudget
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hlong := W.long
  have hlongNN : S.tau W.m <= delta ^ P.epsilon * S.theta W.m := by
    change (S.tau W.m : ENNReal) <=
      (delta : ENNReal) ^ P.epsilon * (S.theta W.m : ENNReal) at hlong
    rw [← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne' P.epsilon,
      ← ENNReal.coe_mul] at hlong
    exact_mod_cast hlong
  have htauDelta : S.tau W.m <= delta ^ P.epsilon := by
    calc
      S.tau W.m <= delta ^ P.epsilon * S.theta W.m := hlongNN
      _ <= delta ^ P.epsilon * 1 :=
        mul_le_mul_of_nonneg_left (S.theta_le_one W.m) (by positivity)
      _ = delta ^ P.epsilon := mul_one _
  have hbTau : canonicalBufferedRadius W <=
      (S.tau W.m) ^ (1 - P.epsilon) := by
    simpa only [canonicalBufferedRadius] using
      (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale_le_tau_rpow_one_sub
        (S.theta_le_one W.m) P.epsilon_pos.le)
  have hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  have hbaseScalar := fixedConflict_baseScalar_le_of_longBufferedScale
    hD.delta_pos hdeltaOne htau
      (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
      htauDelta hbTau hetaThird hbaseScaleGain hCKTfinite hCKTone hCKT
      hbaseAbsorbEta hdeltaBase hbaseBudget
  have hvolume : D.actualFamilyVolume ≠ 0 :=
    actualFamilyVolume_ne_zero_of_frostmanDensity D hD hFsource
  have hindex : Nonempty index :=
    nonempty_of_actualFamilyVolume_ne_zero D hvolume
  have hfine : E.family.refinement.refined.Nonempty := by
    obtain ⟨i⟩ := hindex
    dsimp only [E]
    rw [fullRefinementDatum_refined]
    exact ⟨i, Finset.mem_univ i⟩
  obtain ⟨selected, hselected, hthird⟩ :=
    exists_canonicalBufferedTauActive_frozenOuter_le_gammaThirdFactor_of_fixedConflict
      E hE C S P W hepsilonHalf hbufferedSixteenth
        hFthird hbeta hgammaTwo Pcoarse Y A hCKTfinite hKTEvery hdelta0
        hfine hC htauSmall hsourceP0 hsourceLower hdensityScalar hbaseScalar
  refine ⟨A, hAloss, k, hk, hkpositive, ?_⟩
  exact ⟨
    { selected := selected
      selected_nonempty := hselected
      bound := by
        simpa only [Fintype.card_fin] using hthird }⟩

#print axioms
  exists_fullRefinement_coreNativeTauActive_sameObject_gammaThirdBundle

end
end Family8NormalizedLongCoreTauActiveSameObjectGammaThirdBundleV1
