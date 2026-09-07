import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Family8Grounding.Family8EighthNormalizedSelectedFrostmanThirdFactorV3
import Family8Grounding.Family8NormalizedLongCoreTauActiveParameterLadderBaseFloorV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1
import Family8Grounding.Family8StickyActiveFrozenCoarseSourceMassFrostmanScaleSupportV1
import Family8Grounding.Family8StickyActiveRestrictedCoarseB2SupportV1
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Mathlib.Tactic

/-!
# Fixed-conflict frozen third factor on the normalized long core

This is the Core-native analogue of the old identified-witness third-factor
endpoint.  It works on the literal tau-active cover and the exact bounded
partition/assembly supplied by the normalized long core.  Radius-two support,
the normalized conflict cap, Katz--Tao card-scale control, and the canonical
parameter-ladder base floor are all produced internally.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreTauActiveFrozenOuterGammaThirdFactorFixedConflictV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveParameterLadderBaseFloorV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1.StickyScaleCover
open Family8StickyActiveFrozenCoarseSourceMassFrostmanScaleSupportV1
open Family8StickyActiveRestrictedCoarseB2SupportV1
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyActiveCoarseB2SupportV5
open Family8StickyParentHullVolumeBoundV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The actual frozen-coarse average on a normalized-core bounded assembly
obeys the official Section-8 third-factor estimate. -/
theorem exists_canonicalBufferedTauActive_frozenOuter_le_gammaThirdFactor_of_fixedConflict
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {epsilon etaF : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters gamma epsilon etaF delta0)
    (hbeta : 0 < beta) (hgammaTwo : gamma <= 2)
    (Pcoarse : CoarseTubePartition
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD C S W
          P.epsilon_pos.le hepsilonHalf))
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD C S W
          P.epsilon_pos.le hepsilonHalf)).coarse)
    (Y : Shading
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD C S W
          P.epsilon_pos.le hepsilonHalf)).bodyFamily)
    {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      Pcoarse.asConvexFactorization Y r)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hKTEvery : C.base.IsKatzTaoAtEveryScale CKT)
    (hdelta0 : canonicalBufferedRadius W / 8 <= delta0)
    (hfine : D.family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover
          W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m <=
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
          (((S.tau W.m ^
              (10 * P.eta W.stage / (P.epsilon * beta)) : NNReal) : ENNReal) /
            128)) :
    exists selected : Finset
        (Fin (activeFineRestrictedScaleCover
          (canonicalBufferedTauActiveCover D hD C S W
            P.epsilon_pos.le hepsilonHalf)).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        eighthSelectedThirdFactorLoss (canonicalBufferedRadius W)
            ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal) epsilon gamma *
          sectionEightScaleCountFrostmanFactor
            (canonicalBufferedRadius W) 1
            (activeFineRestrictedScaleCover
              (canonicalBufferedTauActiveCover D hD C S W
                P.epsilon_pos.le hepsilonHalf)).coarseCard gamma := by
  let U0 := canonicalBufferedTauActiveCover D hD C S W
    P.epsilon_pos.le hepsilonHalf
  have hrhoPos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenHalf
  have hKT : U0.IsKatzTaoAtScale CKT :=
    hKTEvery (canonicalBufferedRadius W)
      ((S.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
      (canonicalBufferedRadius_le_one W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf)
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hfamily : U0.activeCoarseFamily = G.activeCoarseFamily :=
    canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global
      D hD C S W P.epsilon_pos.le hepsilonHalf
  have hB2 : forall q,
      ((activeFineRestrictedScaleCover U0).coarse.tubes q).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
    intro q
    let e : {k // k ∈ U0.activeCoarse} ≃ Fin U0.activeCoarse.card :=
      U0.activeCoarse.equivFin
    let k : {k // k ∈ U0.activeCoarse} := e.symm q
    have hsupport := activeCoarseFamily_body_subset_closedBall_two
      D hD G hbufferedSixteenth k
    have hbody : U0.activeCoarseFamily k = G.activeCoarseFamily k :=
      congrFun hfamily k
    change (U0.activeCoarseFamily k : Set Space) ⊆
      Metric.closedBall (0 : Space) 2
    rw [hbody]
    exact hsupport
  have hKTcoarse : IsKatzTao CKT
      (activeFineRestrictedScaleCover U0).coarse.bodyFamily :=
    activeFineRestrictedScaleCover_coarse_isKatzTao U0 hKT
  have hKTdatum : IsKatzTao CKT
      (frozenCoarseActualDatum Pcoarse Y A).family.bodyFamily := by
    simpa only [frozenCoarseActualDatum_family, U0] using hKTcoarse
  have hconflict : forall k,
      (normalizedConflictIndices
        (frozenCoarseActualDatum Pcoarse Y A) k).card <=
          Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) := by
    intro k
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      (frozenCoarseActualDatum Pcoarse Y A) hrhoPos hrhoHalf
        hCKTfinite hKTdatum k
  have hcontained : forall k,
      (U0.activeCoarseFamily k : Set Space) <=
        (closedBallFourBody : Set Space) := by
    intro k
    rw [hfamily]
    exact activeCoarseFamily_body_subset_closedBall_four
      D hD G (hrhoHalf.trans (by norm_num)) k
  have hXUpper : (activeCoarseCardScaleMass U0 : ENNReal) <= 1024 * CKT :=
    activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale_of_contained
      U0 hrhoHalf hKT hcontained
  have hbaseLower :=
    parameterLadder_global_rpow_coe_le_coreCanonicalBufferedTauActiveCardScaleMass
      D hD C S P W hbeta hepsilonHalf hrhoHalf hfine hC htauSmall
  obtain ⟨selected, hselected, haverage⟩ :=
    exists_normalized_activeFrozenCoarse_of_sourceMass_scaleSupport
      hF U0 Pcoarse Y A hrhoPos hrhoHalf hB2 hconflict hKT hdelta0
        hsource0 hsourceLower hXUpper hdensityScalar hbaseLower hbaseScalar
  have htransport :=
    loss_mul_selectedRHS_le_eighthLoss_mul_thirdFactor
      (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
        (frozenCoarseActualDatum Pcoarse Y A)) selected
      (loss := ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
        ENNReal))
      (epsilon := epsilon) (gamma := gamma) hrhoPos hrhoHalf hgammaTwo
  refine ⟨selected, hselected, haverage.trans ?_⟩
  simpa only [Fintype.card_fin] using htransport

#print axioms
  exists_canonicalBufferedTauActive_frozenOuter_le_gammaThirdFactor_of_fixedConflict

end
end Family8NormalizedLongCoreTauActiveFrozenOuterGammaThirdFactorFixedConflictV1
