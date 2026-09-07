import Family8Grounding.Family8CanonicalBufferedTauActiveBoundedFrozenAssemblySourceAverageV1
import Family8Grounding.Family8CanonicalBufferedTauActiveBoundedSourceFloorV3
import Family8Grounding.Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorFixedConflictV1
import Family8Grounding.Family8CanonicalBufferedTauActiveFrozenOuterThirdScalarPowerV1
import Family8Grounding.Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8IdentifiedDividingWitnessFirstOuterParentTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveSameObjectThirdFactorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8IdentifiedDividingWitnessTauActivePowerProductV3.Witness
open Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8TauActiveNativeKatzTaoTransportV4.Witness
open Family8StickyParentHullVolumeBoundV1
open Family8CanonicalBufferedTauActiveBoundedFrozenAssemblySourceAverageV1.Witness
open Family8CanonicalBufferedTauActiveBoundedSourceFloorV3.Witness
open Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorFixedConflictV1.Witness
open Family8CanonicalBufferedTauActiveFrozenOuterThirdScalarPowerV1.Witness
open Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4
open Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness

noncomputable section

/-!
# Same-object tau-active middle/third orchestration

The global `delta -> b` bounded assembly and the tau-active `tau -> b`
bounded assembly are different dependent objects.  This module therefore
uses the literal tau-active bounded assembly throughout.  Its structural
source-average product and the fixed-conflict frozen-outer Frostman endpoint
are composed on the same `Pcoarse`, `A`, and surviving final fibre.

Every assembly-dependent hypothesis of the third endpoint is discharged
internally.  The only remaining density input is a single object-independent
power comparison.  The output deliberately leaves the average multiplicity
of the displayed `finalFiberShading A k`: an analytic estimate for that exact
fibre is the genuine middle-scale producer still required by the long
interval argument.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem exists_fullRefinement_canonicalBufferedTauActive_sameObject_thirdFactor
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {etaSource etaKTSource etaThird epsilonThird etaKT lossEta
      fiberAbsorbEta conflictAbsorbEta baseAbsorbEta : Real}
    {delta0 : NNReal}
    (hFsource : FrostmanHypotheses D etaSource)
    (hKTsource : KatzTaoHypotheses D etaKTSource)
    (hFthird : FrostmanAtParameters beta epsilonThird etaThird delta0)
    (hbeta : 0 < beta) (hbetaTwo : beta <= 2)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hCKTone : 1 <= CKT)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
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
      (Sseq.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : Sseq.tau W.m <=
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
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal)) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U0 := canonicalBufferedTauActiveCover E hE Cmulti Sseq W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E Cmulti Sseq W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let M := Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
      (Sseq.tau W.m) (canonicalBufferedRadius W) CKT
    let hsource0 :
        (IndexedShadingRefinement.restrictTo Dtau.shading
          U0.activeFine).shading.shadingMass ≠ 0 := by
      have hmass : D.shading.shadingMass ≠ 0 := by
        have hfloor : (delta : ENNReal) ^ (2 * etaSource) <=
            D.shading.shadingMass :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
        have hpositive : 0 < (delta : ENNReal) ^ (2 * etaSource) :=
          ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
            ENNReal.coe_ne_top
        exact ne_of_gt (hpositive.trans_le hfloor)
      exact canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        E hE Cmulti Sseq P W hepsilonHalf
          (fullRefinement_sourceTau_activeMass_ne_zero
            D Cmulti Sseq W.m hmass)
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      activeFineRestrictedSourceMass_ne_zero U0 Dtau.shading hsource0
    let hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card <= M :=
      activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
        U0
          (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
          ((tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
            (hbufferedSixteenth.trans (by
              change (1 : Real) / 16 <= (2 : Real)⁻¹
              norm_num)))
          (hbufferedSixteenth.trans (by
            change (1 : Real) / 16 <= (1 : Real)
            norm_num))
          hCKTfinite
          (tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
            E Cmulti Sseq W
              (hKTEvery (Sseq.tau W.m)
                (Sseq.delta_le_tau W.m)
                ((Sseq.tau_le_theta W.m).trans (Sseq.theta_le_one W.m))))
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
        exists selected : Finset (Fin U.coarseCard),
          selected.Nonempty /\
          A.frozenCoarse.averageMultiplicity <=
            Family8EighthNormalizedSelectedFrostmanThirdFactorV3.eighthSelectedThirdFactorLoss
                (canonicalBufferedRadius W)
                ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                  ENNReal) epsilonThird beta *
              Family8ThreeScaleFrostmanFactorAlgebraV2.sectionEightScaleCountFrostmanFactor
                (canonicalBufferedRadius W) 1 U.coarseCard beta /\
          Dtau.shading.averageMultiplicity <=
            (4 * (A.loss : ENNReal)) *
              ((Family8EighthNormalizedSelectedFrostmanThirdFactorV3.eighthSelectedThirdFactorLoss
                  (canonicalBufferedRadius W)
                  ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                    ENNReal) epsilonThird beta *
                Family8ThreeScaleFrostmanFactorAlgebraV2.sectionEightScaleCountFrostmanFactor
                  (canonicalBufferedRadius W) 1 U.coarseCard beta) *
                (finalFiberShading A k).averageMultiplicity) /\
          D.shading.averageMultiplicity <=
            (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
                delta (Sseq.tau W.m)
                  ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) *
              ((4 * (A.loss : ENNReal)) *
                ((Family8EighthNormalizedSelectedFrostmanThirdFactorV3.eighthSelectedThirdFactorLoss
                    (canonicalBufferedRadius W)
                    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                      ENNReal) epsilonThird beta *
                  Family8ThreeScaleFrostmanFactorAlgebraV2.sectionEightScaleCountFrostmanFactor
                    (canonicalBufferedRadius W) 1 U.coarseCard beta) *
                  (finalFiberShading A k).averageMultiplicity)) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U0 := canonicalBufferedTauActiveCover E hE Cmulti Sseq W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E Cmulti Sseq W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  let M := Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
    (Sseq.tau W.m) (canonicalBufferedRadius W) CKT
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor : (delta : ENNReal) ^ (2 * etaSource) <=
        D.shading.shadingMass :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
    have hpositive : 0 < (delta : ENNReal) ^ (2 * etaSource) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hsourceTau := fullRefinement_sourceTau_activeMass_ne_zero
    D Cmulti Sseq W.m hmass
  have hsource0 :
      (IndexedShadingRefinement.restrictTo Dtau.shading
        U0.activeFine).shading.shadingMass ≠ 0 :=
    canonicalBufferedTauActiveCover_restrictedMass_ne_zero
      E hE Cmulti Sseq P W hepsilonHalf hsourceTau
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero U0 Dtau.shading hsource0
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have htauHalf : Sseq.tau W.m <= (2 : NNReal)⁻¹ :=
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
      (hbufferedSixteenth.trans hsixteenHalf)
  have hsixteenOne : (1 / 16 : NNReal) <= 1 := by
    change (1 : Real) / 16 <= (1 : Real)
    norm_num
  have hbOne : canonicalBufferedRadius W <= 1 :=
    hbufferedSixteenth.trans hsixteenOne
  have hKTtau : IsKatzTao CKT Dtau.family.bodyFamily :=
    tauActiveCoarseDatum_isKatzTao_of_tauScaleCover
      E Cmulti Sseq W
        (hKTEvery (Sseq.tau W.m)
          (Sseq.delta_le_tau W.m)
          ((Sseq.tau_le_theta W.m).trans (Sseq.theta_le_one W.m)))
  have hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card <= M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      U0 (hD.delta_pos.trans_le (Sseq.delta_le_tau W.m))
        htauHalf hbOne hCKTfinite hKTtau
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
    hcoarse M hM
  obtain ⟨A, hAloss, k, hk, hkpositive, _hproduct, hsourceProduct⟩ :=
    exists_fullRefinement_canonicalBufferedTauActive_bounded_sourceAverageProduct
      D hD Cmulti Sseq P W hepsilonHalf hbufferedSixteenth
        hFsource hCKTfinite hKTEvery
  have hsourceLower :
      (delta : ENNReal) ^ (2 * etaSource) /
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) <=
        (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass :=
    fullRefinement_canonicalBufferedTauActive_bounded_sourceMass_lower_exactCap
      D hD Cmulti Sseq P W hepsilonHalf hbufferedSixteenth
        hFsource hKTsource hCKTfinite hKTEvery
  have hsourceP0 :
      (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingMass ≠ 0 := by
    have hfloorPos : 0 <
        (delta : ENNReal) ^ (2 * etaSource) /
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
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
      E hE Cmulti Sseq P W hepsilonHalf hCKTfinite hCKTone hCKT
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
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
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
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) :=
        hdensityPowerBudget
  have htau : 0 < Sseq.tau W.m :=
    hD.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  have hlong := W.long
  have hlongNN : Sseq.tau W.m <=
      delta ^ P.epsilon * Sseq.theta W.m := by
    change (Sseq.tau W.m : ENNReal) <=
      (delta : ENNReal) ^ P.epsilon * (Sseq.theta W.m : ENNReal) at hlong
    rw [← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne' P.epsilon,
      ← ENNReal.coe_mul] at hlong
    exact_mod_cast hlong
  have htauDelta : Sseq.tau W.m <= delta ^ P.epsilon := by
    calc
      Sseq.tau W.m <= delta ^ P.epsilon * Sseq.theta W.m := hlongNN
      _ <= delta ^ P.epsilon * 1 :=
        mul_le_mul_of_nonneg_left (Sseq.theta_le_one W.m) (by positivity)
      _ = delta ^ P.epsilon := mul_one _
  have hbTau : canonicalBufferedRadius W <=
      (Sseq.tau W.m) ^ (1 - P.epsilon) := by
    simpa only [canonicalBufferedRadius] using
      (Family8CanonicalLowerBufferedScaleV4.canonicalLowerBufferedScale_le_tau_rpow_one_sub
        (Sseq.theta_le_one W.m) P.epsilon_pos.le)
  have hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  have hbaseScalar := fixedConflict_baseScalar_le_of_longBufferedScale
    hD.delta_pos hdeltaOne htau
      (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
      htauDelta hbTau hetaThird hbaseScaleGain hCKTfinite hCKTone hCKT
      hbaseAbsorbEta hdeltaBase hbaseBudget
  have hvolume : D.actualFamilyVolume ≠ 0 :=
    actualFamilyVolume_ne_zero_of_frostmanDensity D hD hFsource
  have hindex : Nonempty index := nonempty_of_actualFamilyVolume_ne_zero D hvolume
  have hfine : E.family.refinement.refined.Nonempty := by
    obtain ⟨i⟩ := hindex
    dsimp only [E]
    rw [fullRefinementDatum_refined]
    exact ⟨i, Finset.mem_univ i⟩
  obtain ⟨selected, hselected, hthird⟩ :=
    exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_fixedConflict
      E hE Cmulti Sseq P W hepsilonHalf hbufferedSixteenth
        hFthird hbeta hbetaTwo Pcoarse Y A hCKTfinite hKTEvery hdelta0
        hfine hC htauSmall hsourceP0 hsourceLower
        hdensityScalar hbaseScalar
  refine ⟨A, hAloss, k, hk, hkpositive, selected, hselected, hthird, ?_, ?_⟩
  calc
    Dtau.shading.averageMultiplicity <=
        (4 * (A.loss : ENNReal)) *
          (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := hsourceProduct
    _ <= (4 * (A.loss : ENNReal)) *
          ((Family8EighthNormalizedSelectedFrostmanThirdFactorV3.eighthSelectedThirdFactorLoss
              (canonicalBufferedRadius W)
              ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                ENNReal) epsilonThird beta *
            Family8ThreeScaleFrostmanFactorAlgebraV2.sectionEightScaleCountFrostmanFactor
              (canonicalBufferedRadius W) 1 U.coarseCard beta) *
            (finalFiberShading A k).averageMultiplicity) :=
      mul_le_mul' le_rfl (mul_le_mul' hthird le_rfl)
  have hfirst :=
    fullRefinement_averageMultiplicity_le_hypothesisCap_mul_sourceTauParent
      D hD Cmulti Sseq W.m hKTsource
  calc
    D.shading.averageMultiplicity <=
        (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) *
          Dtau.shading.averageMultiplicity := hfirst
    _ <=
        (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal) *
          ((4 * (A.loss : ENNReal)) *
            ((Family8EighthNormalizedSelectedFrostmanThirdFactorV3.eighthSelectedThirdFactorLoss
                (canonicalBufferedRadius W)
                ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                  ENNReal) epsilonThird beta *
              Family8ThreeScaleFrostmanFactorAlgebraV2.sectionEightScaleCountFrostmanFactor
                (canonicalBufferedRadius W) 1 U.coarseCard beta) *
              (finalFiberShading A k).averageMultiplicity)) := by
      apply mul_le_mul' le_rfl
      calc
        Dtau.shading.averageMultiplicity <=
            (4 * (A.loss : ENNReal)) *
              (A.frozenCoarse.averageMultiplicity *
                (finalFiberShading A k).averageMultiplicity) := hsourceProduct
        _ <= (4 * (A.loss : ENNReal)) *
              ((Family8EighthNormalizedSelectedFrostmanThirdFactorV3.eighthSelectedThirdFactorLoss
                  (canonicalBufferedRadius W)
                  ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                    ENNReal) epsilonThird beta *
                Family8ThreeScaleFrostmanFactorAlgebraV2.sectionEightScaleCountFrostmanFactor
                  (canonicalBufferedRadius W) 1 U.coarseCard beta) *
                (finalFiberShading A k).averageMultiplicity) :=
          mul_le_mul' le_rfl (mul_le_mul' hthird le_rfl)

#print axioms
  exists_fullRefinement_canonicalBufferedTauActive_sameObject_thirdFactor

end Witness
end
end Family8CanonicalBufferedTauActiveSameObjectThirdFactorV1
