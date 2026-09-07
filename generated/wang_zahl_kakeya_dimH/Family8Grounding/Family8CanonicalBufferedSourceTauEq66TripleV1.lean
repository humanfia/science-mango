import Family8Grounding.Family8CanonicalBufferedSourceTauFullCoarseTripleV1
import Family8Grounding.Family8CanonicalGlobalOuterScaleCountIdentityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedSourceTauEq66TripleV1

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
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8CanonicalBufferedGlobalFullCoarseDatumV1.Witness
open Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly
open Family8ExplicitConcentrationCanonicalScalarBudgetsV1
open Family8ExplicitConcentrationGeneralizedReturnV1
open Family8CanonicalBufferedGlobalLongIntervalOuterEndpointV1
open Family8CanonicalGlobalOuterParameterAllocationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-!
# Insert Equation (66) into the literal source-tau product

This is the same-object composition of the source-tau frozen product and the
literal full `T_b` long-interval estimate.  The result is associated as

`(4 * frozenLoss * frozenAverage) *
  ((delta^gain * Section8Factor(b, 1, |T_b|)) * finalFiberAverage)`.

No comparison between the full coarse average and the restricted frozen
average is used: average multiplicity is not monotone under shading
restriction.  The full average is inserted by its genuine lower bound one
and then bounded by Equation (66).
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma propertyEta : Real}

theorem exists_canonicalBuffered_sourceTau_eq66_frozenTriple
    {delta0 : NNReal}
    (P : ParameterLadder epsilon0 beta gamma)
    (hKTP : KatzTaoAtParameters beta (sectionEightFixedNu P)
      propertyEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (Aouter : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hpropertyEta : 0 < propertyEta)
    (hfine : D.family.refinement.refined.Nonempty)
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
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D Cmulti Sseq W.m).activeFine).shading.shadingMass ≠ 0) :
    let rho := canonicalBufferedRadius W
    let hbuffered : Sseq.IsBuffered P.epsilon W.m rho :=
      canonicalBufferedRadius_isBuffered
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf
    let Y := sourceTauFullShading D Cmulti Sseq W.m
    let U := bufferedIntervalCover D hD Cmulti Sseq P.epsilon
      P.epsilon_pos.le W.m rho hbuffered
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        D hD Cmulti Sseq P.epsilon P.epsilon_pos.le W.m rho hbuffered hsourceTau
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            D hD Sseq P.epsilon_pos.le W.m rho hbuffered) Y hsource).asConvexFactorization
          Y 1,
      A.loss = frozenComparableLoss
          (bufferedLowerIndex D Cmulti Sseq W.m) (Fin U.coarseCard) /\
      exists k : Fin U.coarseCard, k ∈ U.activeCoarse /\
        0 < volume (finalFiberShading A k).shadedUnion /\
        (parentAggregatedShading (sourceTauCover D Cmulti Sseq W.m)
            D.shading).averageMultiplicity <=
          ((4 * (frozenComparableLoss
              (bufferedLowerIndex D Cmulti Sseq W.m)
                (Fin U.coarseCard) : ENNReal)) *
              A.frozenCoarse.averageMultiplicity) *
            (((delta : ENNReal) ^ (10 * P.eta W.stage) *
                sectionEightScaleCountFrostmanFactor
                  (canonicalBufferedRadius W) 1
                  (canonicalBufferedGlobalCover W hD.delta_pos
                    P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma) *
              (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  let rho := canonicalBufferedRadius W
  let hbuffered : Sseq.IsBuffered P.epsilon W.m rho :=
    canonicalBufferedRadius_isBuffered
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf
  let U := bufferedIntervalCover D hD Cmulti Sseq P.epsilon
    P.epsilon_pos.le W.m rho hbuffered
  obtain ⟨A, hLoss, k, hk, hFiber, hProduct⟩ :=
    Family8CanonicalBufferedSourceTauFullCoarseTripleV1.Witness.exists_canonicalBuffered_sourceTau_fullCoarse_frozenTriple
      D hD Cmulti Sseq P W hepsilonHalf hfine hsourceTau
  refine ⟨A, hLoss, k, hk, hFiber, hProduct.trans ?_⟩
  have hEq66 :=
    Family8CanonicalBufferedGlobalLongIntervalMiddleFactorV1.Witness.canonicalBufferedGlobalFullCoarse_averageMultiplicity_le_middleFactor
      P hKTP D hD Cmulti Sseq W Aouter hbeta hgamma hepsilonHalf
        hpropertyEta hfine hbufferedSixteenth hAone hKTEvery hscalarSmall
        houterSmall hdelta0 hlongScaleSmall hcoefficientPower hC htauSmall hAKT
  have hFactor :=
    Family8CanonicalGlobalOuterScaleCountIdentityV1.activeCoarseCardScaleMass_middleFactor_eq_sectionEight
      (canonicalBufferedGlobalCover W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf) gamma
  rw [hFactor] at hEq66
  calc
    (4 * (frozenComparableLoss
          (bufferedLowerIndex D Cmulti Sseq W.m)
            (Fin U.coarseCard) : ENNReal)) *
        ((canonicalBufferedGlobalFullCoarseDatum D Cmulti Sseq W
            hD.delta_pos P.epsilon_pos.le
              hepsilonHalf).shading.averageMultiplicity *
          (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity)) <=
      (4 * (frozenComparableLoss
          (bufferedLowerIndex D Cmulti Sseq W.m)
            (Fin U.coarseCard) : ENNReal)) *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              (canonicalBufferedRadius W) 1
              (canonicalBufferedGlobalCover W hD.delta_pos
                P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma) *
          (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity)) :=
      mul_le_mul' le_rfl (mul_le_mul' hEq66 le_rfl)
    _ =
      ((4 * (frozenComparableLoss
          (bufferedLowerIndex D Cmulti Sseq W.m)
            (Fin U.coarseCard) : ENNReal)) *
          A.frozenCoarse.averageMultiplicity) *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              (canonicalBufferedRadius W) 1
              (canonicalBufferedGlobalCover W hD.delta_pos
                P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma) *
          (finalFiberShading A k).averageMultiplicity) := by
      ac_rfl

#print axioms exists_canonicalBuffered_sourceTau_eq66_frozenTriple

end Witness
end
end Family8CanonicalBufferedSourceTauEq66TripleV1
