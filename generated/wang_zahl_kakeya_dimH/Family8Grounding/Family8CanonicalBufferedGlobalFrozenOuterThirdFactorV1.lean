import Family8Grounding.Family8CanonicalBufferedGlobalFrozenOuterFrostmanEndpointV2
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalXLowerV2
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedGlobalFrozenOuterThirdFactorV1

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
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8CanonicalBufferedGlobalFrozenOuterFrostmanEndpointV2.Witness
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# Canonical global frozen outer factor

This specializes the source-mass endpoint to the literal parameter-ladder
global cover.  The normalized conflict degree is produced from the actual
Katz--Tao coarse family, and the base floor is the genuine canonical
Frostman `X` lower bound.  Thus only the two scalar power budgets remain.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem exists_canonicalBufferedGlobal_frozenOuter_of_fixedConflict
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth :
      canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {epsilon etaF : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon etaF delta0)
    (hbeta : 0 < beta)
    (Pcoarse : CoarseTubePartition
      (activeFineRestrictedFamily
        (canonicalBufferedGlobalCover W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf))
      (activeFineRestrictedScaleCover
        (canonicalBufferedGlobalCover W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf)).coarse)
    (Y : Shading
      (activeFineRestrictedFamily
        (canonicalBufferedGlobalCover W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf)).bodyFamily)
    {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      Pcoarse.asConvexFactorization Y r)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (hdelta0 : canonicalBufferedRadius W / 8 <= delta0)
    (hfine : D.family.refinement.refined.Nonempty)
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
          (canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf)).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        (((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal) *
          frostmanMultiplicityRHS (canonicalBufferedRadius W / 8)
            (restrictActualTubeDatum
              (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
                (frozenCoarseActualDatum Pcoarse Y A))
              selected).actualFamilyVolume epsilon beta) := by
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hrhoPos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenHalf
  have hGKT : G.IsKatzTaoAtScale CKT :=
    hKTEvery (canonicalBufferedRadius W)
      ((Sseq.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
      (canonicalBufferedRadius_le_one W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf)
  have hKTcoarse : IsKatzTao CKT
      (activeFineRestrictedScaleCover G).coarse.bodyFamily :=
    activeFineRestrictedScaleCover_coarse_isKatzTao G hGKT
  have hKTdatum : IsKatzTao CKT
      (frozenCoarseActualDatum Pcoarse Y A).family.bodyFamily := by
    simpa only [frozenCoarseActualDatum_family, G] using hKTcoarse
  have hconflict : forall k,
      (normalizedConflictIndices
        (frozenCoarseActualDatum Pcoarse Y A) k).card <=
          Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) := by
    intro k
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      (frozenCoarseActualDatum Pcoarse Y A) hrhoPos hrhoHalf
        hCKTfinite hKTdatum k
  have hbaseLowerNN :=
    Family8IdentifiedDividingWitnessCanonicalXLowerV2.Witness.parameterLadder_global_rpow_le_canonicalBufferedCardScaleMass
      D hD Cmulti Sseq P W hbeta hepsilonHalf hrhoHalf hfine hC htauSmall
  have hbaseLower :
      ((Sseq.tau W.m ^
          (10 * P.eta W.stage / (P.epsilon * beta)) : NNReal) : ENNReal) <=
        (activeCoarseCardScaleMass G : ENNReal) := by
    exact_mod_cast hbaseLowerNN
  exact exists_canonicalBufferedGlobal_normalizedFrozenOuter_of_sourceMass
    D hD Cmulti Sseq W P.epsilon_pos.le hepsilonHalf
      hbufferedSixteenth hF Pcoarse Y A hconflict hKTEvery hdelta0
      hsource0 hsourceLower hdensityScalar hbaseLower hbaseScalar

#print axioms
  exists_canonicalBufferedGlobal_frozenOuter_of_fixedConflict

end Witness
end
end Family8CanonicalBufferedGlobalFrozenOuterThirdFactorV1
