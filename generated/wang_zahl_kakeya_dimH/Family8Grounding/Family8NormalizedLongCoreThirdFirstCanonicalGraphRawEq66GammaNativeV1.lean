import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveSameObjectGammaThirdBundleV1
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Mathlib.Tactic

/-!
# Third-first canonical graph and raw Equation (66)

The normalized-core third-bundle producer selects a bounded frozen assembly.
This file keeps that exact assembly and only afterwards runs the Family7 graph
selector on it.  The bounded partition and the source-mass partition forget to
the same canonical convex factorization, so no assembly comparison or
reselection is needed.

The result simultaneously contains the gamma-valued official third factor and
the raw graph/frozen product on one literal `R.A`.  Neither conclusion is an
input.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreThirdFirstCanonicalGraphRawEq66GammaNativeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8Family7CoordinateToVerticalB2SupportV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7FirstCrossingFullCoefficientTripleV3
open Family8Family7FullCoefficientGraphCertificateFromFibreFrostmanV3
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalEq66FrozenTripleV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreFirstOuterParentTransportV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongCoreTauActiveRestrictedCoarseB2SupportV2
open Family8NormalizedLongCoreTauActiveSameObjectGammaThirdBundleV1
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8SourceActiveFineActualAverageIdentityV2
open Family8StickyBoundedFiberFactorizationRoundTripV2
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyParentHullVolumeBoundV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Select the official frozen third bundle directly at `gamma`, and then
construct the canonical Family7 graph and raw Eq. (66) on that exact assembly.

The parameter-ladder `beta` is used only by the canonical base-floor payment.
There is no beta Frostman hypothesis, beta-to-gamma transport, or fourth-card
premise.  The graph part introduces only the actual fibre Frostman hypothesis
used by the Family7 selector. -/
theorem exists_fullRefinement_coreNativeGammaThirdFirst_canonicalGraph_rawEq66
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    (fibreCF : ENNReal) (hCFfinite : fibreCF ≠ ∞)
    (hFibres :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      (activeFineRestrictedScaleCover U0).IsFrostmanAtScale fibreCF)
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
      Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4.frozenOuterThirdKatzTaoBaseSmallDeltaThreshold
        baseAbsorbEta)
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
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKTSource)) : ENNReal)) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let M := Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
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
    exists R : SameAssemblyFullCoefficientGraphIdentity
        (activeFineRestrictedFamily U0) U Pcoarse.asConvexFactorization Y
          fibreCF,
      R.A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) /\
      Nonempty (CoreNativeFrozenThirdBundle Pcoarse.asConvexFactorization Y
        R.A (canonicalBufferedRadius W)
          (Family8EighthNormalizedSelectedFrostmanThirdFactorV3.eighthSelectedThirdFactorLoss
            (canonicalBufferedRadius W)
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal) epsilonThird gamma)
          gamma) /\
      D.shading.averageMultiplicity <=
        R.collapsedPrefix (delta := delta)
            (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
              delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKTSource)))
            lossEta *
          R.A.frozenCoarse.averageMultiplicity := by
  dsimp only at hFibres ⊢
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  let M := Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
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
  obtain ⟨A, hAloss, _kThird, _hkThird, _hkThirdPositive, hXgamma⟩ :=
    exists_fullRefinement_coreNativeTauActive_sameObject_gammaThirdBundle
      D hD C S P W hepsilonHalf hbufferedSixteenth hFsource hKTsource
        hFthird hbeta hgammaTwo hCKTfinite hCKTone hKTEvery hCKT hlossEta
        hfiberAbsorbEta hconflictAbsorbEta hbaseAbsorbEta hdeltaLog
        hdeltaFiber hdeltaConflict hdeltaBase hdelta0 hC htauSmall
        hetaThird hbaseScaleGain hbaseBudget hdensityPowerBudget
  obtain ⟨Xgamma⟩ := hXgamma
  have hrho : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hLossPower :
      (frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U0.activeCoarse.card) : ENNReal) <=
          (delta : ENNReal) ^ (-lossEta) := by
    simpa only [U0, E, hE] using
      (canonicalBufferedTauActive_frozenLoss_le_power
        E hE C S P W hepsilonHalf hlossEta hdeltaLog)
  have hActiveAverage :
      (activeFineShading U0 Dtau.shading).averageMultiplicity <=
        (A.loss : ENNReal) *
          (actualRefinementShading A).averageMultiplicity := by
    have havg :=
      restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement A
    have hfineIndices : Pcoarse.fineIndices = Finset.univ := by
      change U.activeFine = Finset.univ
      exact activeFineRestrictedScaleCover_activeFine U0
    change
      (IndexedShadingRefinement.restrictTo Y
        Pcoarse.fineIndices).shading.averageMultiplicity <=
          (A.loss : ENNReal) *
            (actualRefinementShading A).averageMultiplicity at havg
    rw [hfineIndices, restrictTo_univ_averageMultiplicity,
      activeFineRestrictedShading_averageMultiplicity] at havg
    exact havg
  have hTauAverage : Dtau.shading.averageMultiplicity <=
      (A.loss : ENNReal) *
        (actualRefinementShading A).averageMultiplicity := by
    rw [<- canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
      E hE C S P W hepsilonHalf]
    exact hActiveAverage
  have hcoarseCard : U.coarseCard = U0.activeCoarse.card := by
    rfl
  have hLossPower' :
      (frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U.coarseCard) : ENNReal) <=
          (delta : ENNReal) ^ (-lossEta) := by
    rw [hcoarseCard]
    exact hLossPower
  have hAveragePower : Dtau.shading.averageMultiplicity <=
      (delta : ENNReal) ^ (-lossEta) *
        (actualRefinementShading A).averageMultiplicity := by
    calc
      Dtau.shading.averageMultiplicity <=
          (A.loss : ENNReal) *
            (actualRefinementShading A).averageMultiplicity := hTauAverage
      _ = (frozenComparableLoss {i // i ∈ U0.activeFine}
            (Fin U.coarseCard) : ENNReal) *
          (actualRefinementShading A).averageMultiplicity := by
        rw [hAloss]
      _ <= (delta : ENNReal) ^ (-lossEta) *
          (actualRefinementShading A).averageMultiplicity := by
        exact mul_le_mul' hLossPower' le_rfl
  let firstCap : ENNReal :=
    Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
      delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKTSource))
  have hFirst :=
    Family8NormalizedLongCoreFirstOuterParentTransportV2.NormalizedLongIntervalCoreWitness.fullRefinement_averageMultiplicity_le_firstCap_mul_sourceTauParent
      D hD C S P W hKTsource
  have hSourceRetention : D.shading.averageMultiplicity <=
      (firstCap * (delta : ENNReal) ^ (-lossEta)) *
        (actualRefinementShading A).averageMultiplicity := by
    calc
      D.shading.averageMultiplicity <=
          firstCap * Dtau.shading.averageMultiplicity := hFirst
      _ <= firstCap *
          ((delta : ENNReal) ^ (-lossEta) *
            (actualRefinementShading A).averageMultiplicity) :=
        mul_le_mul' le_rfl hAveragePower
      _ = (firstCap * (delta : ENNReal) ^ (-lossEta)) *
          (actualRefinementShading A).averageMultiplicity := by
        ac_rfl
  have hround : Pcoarse.asConvexFactorization =
      toConvexFactorization U := by
    exact boundedFiber_asConvexFactorization_eq_toConvexFactorization
      U (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
        hcoarse M hM
  have hsourceP :
      (IndexedShadingRefinement.restrictTo Y
        Pcoarse.asConvexFactorization.index.fine).shading.shadingMass ≠ 0 := by
    rw [hround, toConvexFactorization_fine]
    exact hsource
  have hfull : ∀ q ∈ Pcoarse.asConvexFactorization.index.coarse,
      IsFrostmanOn fibreCF (activeFineRestrictedFamily U0).bodyFamily
        (Pcoarse.asConvexFactorization.index.fiber q)
        (U.coarse.tubes q).body := by
    intro q hq
    have hqU : q ∈ U.activeCoarse := by
      rw [hround] at hq
      simpa only [toConvexFactorization_coarse] using hq
    have hIn : IsFrostmanIn fibreCF (U.fiberFamily q)
        (U.coarse.tubes q).body := by
      apply isFrostmanIn_iff_concentration_le.mpr
      exact ⟨U.fiber_carrier_subset_parent q, hFibres q hqU⟩
    have hOn : IsFrostmanOn fibreCF
        (activeFineRestrictedFamily U0).bodyFamily
        (U.fiber q) (U.coarse.tubes q).body :=
      (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
        (activeFineRestrictedFamily U0).bodyFamily
        (U.fiber q) (U.coarse.tubes q).body).mpr hIn
    rw [hround]
    simpa only [toConvexFactorization_fiber] using hOn
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hFineB2 : forall i,
      ((activeFineRestrictedFamily U0).tubes i).carrier <=
        Metric.closedBall (0 : Space) 2 := by
    intro i
    have hparent := U.carrier_subset i (by simp only [U,
      activeFineRestrictedScaleCover_activeFine, Finset.mem_univ])
    exact hparent.trans
      (canonicalBufferedTauActiveRestrictedCoarse_carrier_subset_closedBall_two
        E hE C S W P.epsilon_pos.le hepsilonHalf hbufferedSixteenth
          (U.parent i))
  have hverticalB2 : ∀ axis : Fin 3, ∀ i ∈ U.activeFine,
      ((coordinateToVerticalFamily axis
        (activeFineRestrictedFamily U0)).tubes i).carrier <=
          Metric.closedBall (0 : Space) 2 := by
    intro axis i _hi
    exact coordinateToVerticalFamily_carrier_subset_closedBall_two
      axis (activeFineRestrictedFamily U0) hFineB2 i
  obtain ⟨kGraph, _hkGraph, axis, label, hQ⟩ :=
    exists_fullCoefficientGraphCertificate_of_fibresFrostman
      (activeFineRestrictedFamily U0) U Pcoarse.asConvexFactorization
        Y A fibreCF hCFfinite hfull htau hrho hsourceP hround hverticalB2
  dsimp only at hQ
  let baseLoss : ENNReal :=
    (A.loss : ENNReal) *
      (Pcoarse.asConvexFactorization.index.coarse.card : ENNReal)
  let d : ENNReal :=
    (sourceActiveFineShading Pcoarse.asConvexFactorization Y).shadingDensity /
      baseLoss
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss
      (((S.tau W.m : NNReal) : Real) / 2) : Nat) : ENNReal)
  let effectiveCF : ENNReal := fibreCF * (d⁻¹ * graphLoss)
  change Nonempty
    (FirstCrossingFullCoefficientGraphCertificate
      (activeFineRestrictedFamily U0) U Pcoarse.asConvexFactorization
        Y A kGraph axis label effectiveCF d graphLoss) at hQ
  let Qgraph := Classical.choice hQ
  let R : SameAssemblyFullCoefficientGraphIdentity
      (activeFineRestrictedFamily U0) U Pcoarse.asConvexFactorization Y
        fibreCF :=
    { A := A
      k := kGraph
      axis := axis
      label := label
      graphCertificate := Nonempty.intro Qgraph }
  let graphAverage : ENNReal :=
    (firstCrossingFamilyGraphBucketShading axis label
      (activeFineRestrictedFamily U0) Pcoarse.asConvexFactorization A
        kGraph).averageMultiplicity
  let collapsedPrefix : ENNReal :=
    ((firstCap * (4 * (delta : ENNReal) ^ (-lossEta))) * graphLoss) *
      graphAverage
  have hRaw0 :=
    sourceAverage_le_fullCoefficientMiddle_mul_frozenCoarse
      (activeFineRestrictedFamily U0) U Pcoarse.asConvexFactorization
        Y A kGraph axis label effectiveCF d graphLoss
        (firstCap * (delta : ENNReal) ^ (-lossEta))
        D.shading.averageMultiplicity Qgraph hSourceRetention
  have hRaw : D.shading.averageMultiplicity <=
      collapsedPrefix * A.frozenCoarse.averageMultiplicity := by
    calc
      D.shading.averageMultiplicity <=
          (((firstCap * (delta : ENNReal) ^ (-lossEta)) * 4 * graphLoss) *
              graphAverage) * A.frozenCoarse.averageMultiplicity := by
        simpa only [graphAverage] using hRaw0
      _ = collapsedPrefix * A.frozenCoarse.averageMultiplicity := by
        dsimp only [collapsedPrefix]
        ac_rfl
  refine ⟨R, ?_, ?_, ?_⟩
  · simpa only [R] using hAloss
  · exact ⟨by simpa only [R] using Xgamma⟩
  · simpa only [SameAssemblyFullCoefficientGraphIdentity.collapsedPrefix,
      SameAssemblyFullCoefficientGraphIdentity.graphLoss,
      SameAssemblyFullCoefficientGraphIdentity.graphAverage, R,
      collapsedPrefix, graphAverage, graphLoss, firstCap] using hRaw

#print axioms
  exists_fullRefinement_coreNativeGammaThirdFirst_canonicalGraph_rawEq66

end
end Family8NormalizedLongCoreThirdFirstCanonicalGraphRawEq66GammaNativeV1
