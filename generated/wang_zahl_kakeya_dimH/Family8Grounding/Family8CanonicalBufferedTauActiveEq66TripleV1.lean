import Family8Grounding.Family8CanonicalBufferedSourceTauFullCoarseTripleV1
import Family8Grounding.Family8IdentifiedDividingWitnessFirstOuterParentTransportV1
import Family8Grounding.Family8CanonicalGlobalOuterScaleCountIdentityV1
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveEq66TripleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ParameterLadderV1
open Family8LongIntervalBootstrapNumericsV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8IdentifiedDividingWitnessTauActivePowerProductV3.Witness
open Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness
open Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness
open Family8CanonicalBufferedSourceTauFullCoarseTripleV1.Witness
open Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ExplicitConcentrationCanonicalScalarBudgetsV1
open Family8ExplicitConcentrationGeneralizedReturnV1
open Family8CanonicalBufferedGlobalLongIntervalOuterEndpointV1
open Family8CanonicalGlobalOuterParameterAllocationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-!
# Equation (66) on the controlled-loss tau-active assembly

The unreindexed interval assembly has logarithms of its full ambient index
types, which may contain inactive dummy tubes.  This theorem instead uses the
canonical active reindexing, whose two logarithms are controlled at the
original scale, and inserts the literal full `T_b` Equation (66) factor into
that same source product.  The genuine source-to-tau natural fibre cap stays
visible; no standalone power estimate of it is made.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma propertyEta : Real}

theorem exists_fullRefinement_tauActive_eq66_frozenTriple
    {delta0 : NNReal}
    (P : ParameterLadder epsilon0 beta gamma)
    (hKTP : KatzTaoAtParameters beta (sectionEightFixedNu P)
      propertyEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      (fullRefinementDatum D).family Cmulti P.N P.epsilon P.eta Sseq)
    (Aouter : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hpropertyEta : 0 < propertyEta)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal))
    (hAone : 1 <= (Aouter : ENNReal))
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale (Aouter : ENNReal))
    (hscalarSmall : canonicalBufferedRadius W / 8 <=
      canonicalOuterScalarThreshold (Aouter : ENNReal)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta))
    (houterSmall : canonicalBufferedRadius W / 8 <=
      explicitConcentrationGeneralizedReturnThreshold
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (canonicalGlobalOuterQuantum P propertyEta)
        (sectionEightFixedNu P) beta)
    (hdelta0 : canonicalBufferedRadius W / 64 <= delta0)
    (hlongScaleSmall : canonicalBufferedRadius W <=
      Family8ExplicitConcentrationFreshReturnNormalizationV2.explicitConcentrationFreshReturnScaleThreshold
        (canonicalFullCoarseGeneralizedLoss (sectionEightFixedNu P) beta
          (canonicalGlobalOuterQuantum P propertyEta)
          (canonicalGlobalOuterQuantum P propertyEta)
          (canonicalGlobalOuterQuantum P propertyEta)
          (canonicalGlobalOuterQuantum P propertyEta)
          (canonicalGlobalOuterQuantum P propertyEta))
        (canonicalGlobalOuterQuantum P propertyEta))
    (hcoefficientPower : 128 * (Aouter : ENNReal) <=
      (Sseq.tau W.m : ENNReal) ^
        (-canonicalGlobalOuterQuantum P propertyEta))
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
    (hAKT : 1024 * Aouter <=
      Sseq.tau W.m ^
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
    let U := canonicalBufferedTauActiveCover
      E (fullRefinementDatum_isAdmissible hD) Cmulti Sseq W
        P.epsilon_pos.le hepsilonHalf
    let hscale : Sseq.tau W.m <= canonicalBufferedRadius W :=
      tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
    let Y := (tauActiveCoarseDatum E Cmulti Sseq W).shading
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
      exact canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        E (fullRefinementDatum_isAdmissible hD) Cmulti Sseq P W
          hepsilonHalf
          (fullRefinement_sourceTau_activeMass_ne_zero
            D Cmulti Sseq W.m hmass)
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
              delta (Sseq.tau W.m)
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
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
        D.shading.shadingMass :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
    have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
    exact ne_of_gt (hpositive.trans_le hfloor)
  obtain ⟨A, hLoss, k, hFiber, hProduct⟩ :=
    exists_fullRefinement_tauActive_firstOuter_frozenPowerProduct
      D hD Cmulti Sseq P W hepsilonHalf hmass hKTsource
        hlossEta hdeltaLoss
  refine ⟨A, hLoss, k, hFiber, hProduct.trans ?_⟩
  have hvolume : D.actualFamilyVolume ≠ 0 :=
    actualFamilyVolume_ne_zero_of_frostmanDensity D hD hFsource
  obtain ⟨i⟩ := nonempty_of_actualFamilyVolume_ne_zero D hvolume
  have hfine : E.family.refinement.refined.Nonempty := by
    rw [fullRefinementDatum_refined]
    exact ⟨i, Finset.mem_univ i⟩
  have hone := one_le_canonicalBufferedGlobalFullCoarse_averageMultiplicity
    E (fullRefinementDatum_isAdmissible hD) Cmulti Sseq P W
      hepsilonHalf hfine
  have hEq66 :=
    Family8CanonicalBufferedGlobalLongIntervalMiddleFactorV1.Witness.canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_middleFactor
      P hKTP E (fullRefinementDatum_isAdmissible hD) Cmulti Sseq W Aouter
        hbeta hgamma hepsilonHalf hpropertyEta hfine hbufferedSixteenth
        hAone hKTEvery hscalarSmall houterSmall hdelta0 hlongScaleSmall
        hcoefficientPower hC htauSmall hAKT
  have hFactor :=
    Family8CanonicalGlobalOuterScaleCountIdentityV1.activeCoarseCardScaleMass_middleFactor_eq_sectionEight
      (canonicalBufferedGlobalCover W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf) gamma
  rw [hFactor] at hEq66
  calc
    (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
          delta (Sseq.tau W.m)
            ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
        (((4 * (delta : ENNReal) ^ (-lossEta)) *
            A.frozenCoarse.averageMultiplicity) *
          (finalFiberShading A k).averageMultiplicity) =
      ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
              ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
          ((4 * (delta : ENNReal) ^ (-lossEta)) *
            A.frozenCoarse.averageMultiplicity)) *
        (1 * (finalFiberShading A k).averageMultiplicity) := by
      ac_rfl
    _ <=
      ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
              ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
          ((4 * (delta : ENNReal) ^ (-lossEta)) *
            A.frozenCoarse.averageMultiplicity)) *
        ((canonicalBufferedGlobalFullCoarseDatum E Cmulti Sseq W
            hD.delta_pos P.epsilon_pos.le
              hepsilonHalf).shading.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) :=
      mul_le_mul' le_rfl (mul_le_mul' hone le_rfl)
    _ <=
      ((Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
            delta (Sseq.tau W.m)
              ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
          ((4 * (delta : ENNReal) ^ (-lossEta)) *
            A.frozenCoarse.averageMultiplicity)) *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              (canonicalBufferedRadius W) 1
              (canonicalBufferedGlobalCover W hD.delta_pos
                P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma) *
          (finalFiberShading A k).averageMultiplicity) :=
      mul_le_mul' le_rfl (mul_le_mul' hEq66 le_rfl)

#print axioms exists_fullRefinement_tauActive_eq66_frozenTriple

end Witness
end
end Family8CanonicalBufferedTauActiveEq66TripleV1
