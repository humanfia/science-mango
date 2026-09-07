import Family8Grounding.Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorBaseFloorV2
import Family8Grounding.Family8CanonicalBufferedTauActiveFrozenOuterConflictCapV5
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorFixedConflictV1

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
open Family8B2NormalizedConflictKatzTaoCapV3
open Family8B2NormalizedConflictKatzTaoCapV5
open Family8B2NormalizedConflictKatzTaoCapV6
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8CanonicalBufferedTauActiveFrozenOuterConflictCapV5.Witness
open Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorBaseFloorV2.Witness
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-!
# Frozen outer third factor with the fixed exact-incidence conflict loss

The canonical same-assembly conflict producer is substituted into the
parameter-ladder endpoint.  Cancelling the common normalized-radius square
replaces the threshold by the fixed natural ceiling of
`480000 * (128 * CKT)`.  No degree callback remains, and the displayed loss
is immediately compatible with `fixedKatzTaoClosedLoss_coe_le_add_two`.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_fixedConflict
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {epsilon etaF : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon etaF delta0)
    (hbeta : 0 < beta) (hbetaTwo : beta <= 2)
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
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (hdelta0 : canonicalBufferedRadius W / 8 <= delta0)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (Sseq.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : Sseq.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    {sourceFloor : ENNReal}
    (hsource0 :
      (sourceActiveFineShading
        Pcoarse.asConvexFactorization Y).shadingMass ≠ 0)
    (hsourceLower : sourceFloor <=
      (sourceActiveFineShading
        Pcoarse.asConvexFactorization Y).shadingMass)
    (hdensityScalar :
      ((((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ etaF *
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
            (8 * (1024 * CKT))) <= sourceFloor)
    (hbaseScalar :
      ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) *
          ((128 * CKT) * volume (unitBallBody : Set Space)) <=
        (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ (-etaF)) *
          (((Sseq.tau W.m ^
              (10 * P.eta W.stage / (P.epsilon * beta)) : NNReal) : ENNReal) /
            128)) :
    exists selected : Finset
        (Fin (activeFineRestrictedScaleCover
          (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
            P.epsilon_pos.le hepsilonHalf)).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        eighthSelectedThirdFactorLoss (canonicalBufferedRadius W)
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal) epsilon beta *
          sectionEightScaleCountFrostmanFactor
            (canonicalBufferedRadius W) 1
            (activeFineRestrictedScaleCover
              (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
                P.epsilon_pos.le hepsilonHalf)).coarseCard beta := by
  have hrhoPos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hcap :=
    canonicalBufferedTauActive_frozenCoarse_normalizedConflict_card_le
      D hD Cmulti Sseq W P.epsilon_pos.le hepsilonHalf
        hbufferedSixteenth Pcoarse Y A hCKTfinite hKTEvery
  have hcapFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCKTfinite
  have hcapEq := normalizedConflictKatzTaoNatCap_eq_fixed
    hrhoPos hcapFinite
  have hconflict : forall k,
      (normalizedConflictIndices
        (frozenCoarseActualDatum Pcoarse Y A) k).card <=
        Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) := by
    intro k
    simpa only [hcapEq] using hcap k
  exact
    exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_parameterLadderBaseFloor
      D hD Cmulti Sseq P W hepsilonHalf hbufferedSixteenth
        hF hbeta hbetaTwo Pcoarse Y A hconflict hKTEvery hdelta0 hfine
        hC htauSmall hsource0 hsourceLower hdensityScalar hbaseScalar

#print axioms
  exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_fixedConflict

end Witness
end
end Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorFixedConflictV1
