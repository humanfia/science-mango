import Family8Grounding.Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorV3
import Family8Grounding.Family8CanonicalBufferedTauActiveParameterLadderBaseFloorV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorBaseFloorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorV3.Witness
open Family8CanonicalBufferedTauActiveParameterLadderBaseFloorV2.Witness
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-!
# Frozen outer third factor with the actual parameter-ladder base floor

The base cardinality floor in the same-assembly endpoint is the literal
canonical Frostman `X` lower bound.  This successor produces it internally on
the same tau-active cover, so neither an arbitrary `baseFloor` nor a renamed
copy of the desired lower inequality remains among the inputs.  V1 only
missed a namespace and an explicit NNReal fixed-ratio proof.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_parameterLadderBaseFloor
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W ≤ (1 / 16 : NNReal))
    {epsilon etaF : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon etaF delta0)
    (hbeta : 0 < beta) (hbetaTwo : beta ≤ 2)
    (Pcoarse : CoarseTubePartition
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf))
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf)).coarse)
    (Y : Shading
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf)).bodyFamily)
    {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      Pcoarse.asConvexFactorization Y r)
    {conflictThreshold : Nat}
    (hconflict : ∀ k,
      (normalizedConflictIndices
        (frozenCoarseActualDatum Pcoarse Y A) k).card ≤ conflictThreshold)
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (hdelta0 : canonicalBufferedRadius W / 8 ≤ delta0)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody ≤
      (Sseq.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : Sseq.tau W.m ≤
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    {sourceFloor : ENNReal}
    (hsource0 :
      (sourceActiveFineShading
        Pcoarse.asConvexFactorization Y).shadingMass ≠ 0)
    (hsourceLower : sourceFloor ≤
      (sourceActiveFineShading
        Pcoarse.asConvexFactorization Y).shadingMass)
    (hdensityScalar :
      ((((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ etaF *
            ((conflictThreshold + 1 : Nat) : ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
            (8 * (1024 * CKT))) ≤ sourceFloor)
    (hbaseScalar :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * CKT) * volume (unitBallBody : Set Space)) ≤
        (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ (-etaF)) *
          (((Sseq.tau W.m ^
              (10 * P.eta W.stage / (P.epsilon * beta)) : NNReal) : ENNReal) /
            128)) :
    ∃ selected : Finset
        (Fin (activeFineRestrictedScaleCover
          (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
            P.epsilon_pos.le hepsilonHalf)).coarseCard),
      selected.Nonempty ∧
      A.frozenCoarse.averageMultiplicity ≤
        eighthSelectedThirdFactorLoss (canonicalBufferedRadius W)
            ((conflictThreshold + 1 : Nat) : ENNReal) epsilon beta *
          sectionEightScaleCountFrostmanFactor
            (canonicalBufferedRadius W) 1
            (activeFineRestrictedScaleCover
              (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
                P.epsilon_pos.le hepsilonHalf)).coarseCard beta := by
  have hsixteenHalf : (1 / 16 : NNReal) ≤ (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 ≤ (2 : Real)⁻¹
    norm_num
  have hbaseLower :=
    parameterLadder_global_rpow_coe_le_canonicalBufferedTauActiveCardScaleMass
      D hD Cmulti Sseq P W hbeta hepsilonHalf
        (hbufferedSixteenth.trans hsixteenHalf) hfine hC htauSmall
  exact
    exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_everyScale
      D hD Cmulti Sseq W P.epsilon_pos.le hepsilonHalf
        hbufferedSixteenth hF hbetaTwo Pcoarse Y A hconflict hKTEvery hdelta0
        hsource0 hsourceLower hdensityScalar hbaseLower hbaseScalar

#print axioms
  exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_parameterLadderBaseFloor

end Witness
end
end Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorBaseFloorV2
