import Family8Grounding.Family8NormalizedLongCoreEq66FactorOneV2
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8IdentifiedDividingWitnessSourceTauFrozenProductV3
import Family8Grounding.Family8NormalizedLongCoreFirstOuterParentTransportV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveBasicTransportsV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Mathlib.Tactic

/-!
# Canonical Equation (66) frozen triple on a normalized LongCore witness, V2

This replays the source-to-tau frozen product directly on the canonical
tau-active cover of one `NormalizedLongIntervalCoreWitness`.  The global
Equation (66) factor is inserted using its proved lower bound by one.  Thus
the stage, tau scale, canonical buffered scale, cover, shading, assembly,
frozen coarse average, and surviving final fibre are all literal same
objects.

No conversion to an identified witness is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreCanonicalEq66FrozenTripleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyParentHullVolumeBoundV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The literal normalized-W Equation (66) triple.  Its `middleScale` is
`canonicalBufferedRadius W`, its third count is the canonical global active
coarse cardinality, and its third loss is the actual surviving final-fibre
average on the same assembly `A` occurring in the collapsed prefix. -/
theorem exists_fullRefinement_normalizedLongCore_eq66_frozenTriple
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (Aouter : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal))
    (hKTEvery : C.base.IsKatzTaoAtEveryScale (Aouter : ENNReal))
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
    (hAKT : 1024 * Aouter <=
      S.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta))))
    {etaF etaKT lossEta : Real}
    (hFsource : FrostmanHypotheses D etaF)
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hlossEta : 0 < lossEta)
    (hdeltaLoss : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let U := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let hscale : S.tau W.m <= canonicalBufferedRadius W :=
      tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
    let Y := (tauActiveCoarseDatum E C S W).shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hmass : D.shading.shadingMass ≠ 0 := by
        have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
            D.shading.shadingMass :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
        have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
          ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
            ENNReal.coe_ne_top
        exact ne_of_gt (hpositive.trans_le hfloor)
      exact
        Family8NormalizedLongCoreTauActiveBasicTransportsV2.canonicalBufferedTauActiveCover_restrictedMass_ne_zero
          E hE C S P W hepsilonHalf
            (Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
              D C S W.m hmass)
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition
          (activeFineRestrictedScaleCover U) hscale
          (activeFineRestrictedShading U Y)
          (activeFineRestrictedSourceMass_ne_zero U Y hsource)).asConvexFactorization
        (activeFineRestrictedShading U Y) 1,
      A.loss = frozenComparableLoss {i // i ∈ U.activeFine}
          (Fin U.activeCoarse.card) /\
      exists k : Fin U.activeCoarse.card,
        0 < volume (finalFiberShading A k).shadedUnion /\
        D.shading.averageMultiplicity <=
          ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
              delta (S.tau W.m)
                ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
            ((4 * (delta : ENNReal) ^ (-lossEta)) *
              A.frozenCoarse.averageMultiplicity)) *
          (((delta : ENNReal) ^ (10 * P.eta W.stage) *
              sectionEightScaleCountFrostmanFactor
                (canonicalBufferedRadius W) 1
                (canonicalBufferedGlobalCover W hD.delta_pos
                  P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma) *
            (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let U := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Y := (tauActiveCoarseDatum E C S W).shading
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
        D.shading.shadingMass :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
    have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
        ENNReal.coe_ne_top
    exact ne_of_gt (hpositive.trans_le hfloor)
  have hsourceTau :
      (IndexedShadingRefinement.restrictTo E.shading
        (tauScaleCover E C S W).activeFine).shading.shadingMass ≠ 0 :=
    Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
      D C S W.m hmass
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    Family8NormalizedLongCoreTauActiveBasicTransportsV2.canonicalBufferedTauActiveCover_restrictedMass_ne_zero
      E hE C S P W hepsilonHalf hsourceTau
  have hscale : S.tau W.m <= canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  obtain ⟨A, hLoss, hAverage, k, hFiber, hProduct⟩ :=
    exists_activeIndex_frozenComparableAssembly
      U hscale Y 1 (by norm_num) hsource
  have hLossPower :
      (frozenComparableLoss {i // i ∈ U.activeFine}
        (Fin U.activeCoarse.card) : ENNReal) <=
          (delta : ENNReal) ^ (-lossEta) := by
    simpa only [U, E, hE] using
      (canonicalBufferedTauActive_frozenLoss_le_power
        E hE C S P W hepsilonHalf hlossEta hdeltaLoss)
  have hAveragePower : Y.averageMultiplicity <=
      (delta : ENNReal) ^ (-lossEta) *
        (actualRefinementShading A).averageMultiplicity := by
    rw [← Family8NormalizedLongCoreTauActiveBasicTransportsV2.canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
      E hE C S P W hepsilonHalf]
    exact hAverage.trans (mul_le_mul' hLossPower le_rfl)
  have hTauProduct : Y.averageMultiplicity <=
      (4 * (delta : ENNReal) ^ (-lossEta)) *
        (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) := by
    calc
      Y.averageMultiplicity <=
          (delta : ENNReal) ^ (-lossEta) *
            (actualRefinementShading A).averageMultiplicity := hAveragePower
      _ <= (delta : ENNReal) ^ (-lossEta) *
          (4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity)) :=
        mul_le_mul' le_rfl hProduct
      _ = (4 * (delta : ENNReal) ^ (-lossEta)) *
          (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
        ac_rfl
  have hFirst :=
    Family8NormalizedLongCoreFirstOuterParentTransportV2.NormalizedLongIntervalCoreWitness.fullRefinement_averageMultiplicity_le_firstCap_mul_sourceTauParent
      D hD C S P W hKTsource
  have hRaw : D.shading.averageMultiplicity <=
      ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
          delta (S.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
        ((4 * (delta : ENNReal) ^ (-lossEta)) *
          A.frozenCoarse.averageMultiplicity)) *
      (finalFiberShading A k).averageMultiplicity := by
    calc
      D.shading.averageMultiplicity <=
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
              delta (S.tau W.m)
                ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
            Y.averageMultiplicity := by
        exact hFirst
      _ <=
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
              delta (S.tau W.m)
                ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
            ((4 * (delta : ENNReal) ^ (-lossEta)) *
              (A.frozenCoarse.averageMultiplicity *
                (finalFiberShading A k).averageMultiplicity)) :=
        mul_le_mul' le_rfl hTauProduct
      _ =
          ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
              delta (S.tau W.m)
                ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
            ((4 * (delta : ENNReal) ^ (-lossEta)) *
              A.frozenCoarse.averageMultiplicity)) *
          (finalFiberShading A k).averageMultiplicity := by
        ac_rfl
  have hvolume : D.actualFamilyVolume ≠ 0 :=
    actualFamilyVolume_ne_zero_of_frostmanDensity D hD hFsource
  obtain ⟨i⟩ := nonempty_of_actualFamilyVolume_ne_zero D hvolume
  have hfine : E.family.refinement.refined.Nonempty := by
    rw [fullRefinementDatum_refined]
    exact ⟨i, Finset.mem_univ i⟩
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans (by
      change (1 : Real) / 16 <= (2 : Real)⁻¹
      norm_num)
  have hFactorOne : (1 : ENNReal) <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (canonicalBufferedRadius W) 1
          (canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma :=
    Family8NormalizedLongCoreEq66FactorOneV2.one_le_canonicalBufferedGlobal_eq66Factor
      E hE C S P W Aouter hbeta hgamma hepsilonHalf hrhoHalf hfine
        hC htauSmall hKTEvery hAKT
  refine ⟨A, hLoss, k, hFiber, hRaw.trans ?_⟩
  calc
    ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
          delta (S.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
        ((4 * (delta : ENNReal) ^ (-lossEta)) *
          A.frozenCoarse.averageMultiplicity)) *
        (finalFiberShading A k).averageMultiplicity =
      ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
          ((4 * (delta : ENNReal) ^ (-lossEta)) *
            A.frozenCoarse.averageMultiplicity)) *
        (1 * (finalFiberShading A k).averageMultiplicity) := by
      rw [one_mul]
    _ <=
      ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (S.tau W.m)
              ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
          ((4 * (delta : ENNReal) ^ (-lossEta)) *
            A.frozenCoarse.averageMultiplicity)) *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              (canonicalBufferedRadius W) 1
              (canonicalBufferedGlobalCover W hD.delta_pos
                P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma) *
          (finalFiberShading A k).averageMultiplicity) :=
      mul_le_mul' le_rfl (mul_le_mul' hFactorOne le_rfl)

#print axioms exists_fullRefinement_normalizedLongCore_eq66_frozenTriple

end
end Family8NormalizedLongCoreCanonicalEq66FrozenTripleV2
