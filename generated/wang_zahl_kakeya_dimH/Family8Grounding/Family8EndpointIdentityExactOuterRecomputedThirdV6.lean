import Family8Grounding.Family8ActiveFineRestrictedCardScaleMassRefoldV3
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Family8Grounding.Family8EighthNormalizedSelectedFrostmanThirdFactorV3
import Family8Grounding.Family8EndpointIdentityTauActiveCoarseFrostmanKatzTaoV3
import Family8Grounding.Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
import Family8Grounding.Family8ExactOuterRecomputedNeighborhoodCoreNativeThirdBundleV2
import Family8Grounding.Family8IdentityCoreTauActiveSingletonFiberV4
import Family8Grounding.Family8IdentitySourceFrostmanThirdBaseCancellationV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveRestrictedCoarseB2SupportV2
import Family8Grounding.Family8RecomputedNeighborhoodNormalizedDensityBudgetV2
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Mathlib.Tactic

/-!
# Identity endpoint exact-outer recomputed third branch, V6

V1--V5 are frozen visibility, object-refold, and linter drafts.  This clean
successor removes the no-op B2 goal change while retaining the proof-valued
local instance needed by the normalized selector.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityExactOuterRecomputedThirdV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFineRestrictedCardScaleMassRefoldV3
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8CoreNativeFrozenThirdBundleV1
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EndpointIdentityTauActiveCoarseFrostmanKatzTaoV3
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8ExactOuterRecomputedNeighborhoodCoreNativeThirdBundleV2
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8IdentitySourceFrostmanThirdBaseCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveRestrictedCoarseB2SupportV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8RecomputedNeighborhoodActualTubeDatumV2
open Family8RecomputedNeighborhoodNormalizedDensityBudgetV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- On one literal endpoint singleton partition and exact-outer assembly,
source Frostman control supplies the Katz--Tao constant and normalized
conflict cap.  Only the displayed density and base power allocations remain
as scalar premises. -/
theorem nonempty_endpointLongCore_identity_exactOuter_recomputedThird
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth :
      canonicalBufferedRadius W <= (1 / 16 : NNReal))
    (hsourceMass : D.shading.shadingMass ≠ 0)
    {etaSource etaThird epsilonThird betaThird : Real} {delta0 : NNReal}
    (hFsource : FrostmanHypotheses D etaSource)
    (hFthird : FrostmanAtParameters
      betaThird epsilonThird etaThird delta0)
    (hbetaTwo : betaThird <= 2)
    (hdelta0 : canonicalBufferedRadius W / 8 <= delta0) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let rho := canonicalBufferedRadius W
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
        rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf]
        exact hsourceMass
      rw [shadingMass_restrictTo_eq_sum]
      exact hOn
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
      intro k _hk
      simpa only [Fintype.card_coe] using
        identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          E hE S W P.epsilon_pos.le hepsilonHalf k
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse 1 hM
    let CKT := identitySourceFrostmanKatzTaoConstant D rho etaSource
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    forall A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.frozenCoarse =
          Pcoarse.asConvexFactorization.inducedShading
            A.refinement.shading ->
      (((rho / 8 : NNReal) : ENNReal) ^ etaThird *
          (128 *
            ((conflictThreshold + 1 : Nat) : ENNReal)) <=
        Y.shadingDensity ^ 2 /
          ((A.loss : ENNReal) *
            (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2))) ->
      (((conflictThreshold + 1 : Nat) : ENNReal) * 2097152 *
          (delta : ENNReal) ^ (-etaSource) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)) ->
      Nonempty
        (CoreNativeFrozenThirdBundle
          Pcoarse.asConvexFactorization Y A rho
          (eighthSelectedThirdFactorLoss rho
            ((432 : ENNReal) *
              ((conflictThreshold + 1 : Nat) : ENNReal))
            epsilonThird betaThird)
          betaThird) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
    rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
      D hD P W hepsilonHalf]
    exact hsourceMass
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 := by
    rw [shadingMass_restrictTo_eq_sum]
    exact hOn
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
    intro k _hk
    simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf k
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  have hscale : S.tau W.m <= rho :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Pcoarse := boundedFiberCoarseTubePartition U hscale hcoarse 1 hM
  let CKT := identitySourceFrostmanKatzTaoConstant D rho etaSource
  let conflictThreshold :=
    Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
  intro A hfrozen hdensityScalar hbasePower
  letI : Nonempty (Fin U.coarseCard) := by
    obtain ⟨q, _hq⟩ := hcoarse
    exact ⟨q⟩
  have hrhoPos : 0 < rho :=
    canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : rho <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenHalf
  have htauPos : 0 < S.tau W.m := hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hUfine : U.activeFine = Finset.univ := by
    exact activeFineRestrictedScaleCover_activeFine U0
  have hUcoarse : U.activeCoarse = Finset.univ := by
    exact activeFineRestrictedScaleCover_activeCoarse U0
  have hfine : Pcoarse.fineIndices = Finset.univ := by
    change U.activeFine = Finset.univ
    exact hUfine
  have hcoarseIndices : Pcoarse.coarseIndices = Finset.univ := by
    change U.activeCoarse = Finset.univ
    exact hUcoarse
  have hmass : A.refinement.shading.shadingMass ≠ 0 :=
    refinement_shadingMass_ne_zero A (by
      change (IndexedShadingRefinement.restrictTo Y
        Pcoarse.fineIndices).shading.shadingMass ≠ 0
      rw [hfine, ← hUfine]
      exact hsource)
  have hB2 : forall q : Fin U.coarseCard,
      (U.coarse.tubes q).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
    intro q
    simpa only [U, U0, rho, E, hE, C, S] using
      (canonicalBufferedTauActiveRestrictedCoarse_carrier_subset_closedBall_two
        E hE C S W P.epsilon_pos.le hepsilonHalf hbufferedSixteenth q)
  have hKT : IsKatzTao CKT U.coarse.bodyFamily := by
    simpa only [CKT, U, U0, E, hE, C, S, rho] using
      (endpointLongCore_identity_tauActiveRestrictedCoarse_isKatzTao
        D hD P W hepsilonHalf hbufferedSixteenth hFsource)
  have hCfinite : CKT ≠ ∞ := by
    exact identitySourceFrostmanKatzTaoConstant_ne_top
      D rho hD.delta_pos etaSource
  have hdatumKT : IsKatzTao CKT
      (recomputedNeighborhoodActualTubeDatum
        Pcoarse A.refinement.shading).family.bodyFamily :=
    recomputedNeighborhoodActualTubeDatum_isKatzTao
      Pcoarse A.refinement.shading hKT
  have hconflict : forall q : Fin U.coarseCard,
      (normalizedConflictIndices
        (recomputedNeighborhoodActualTubeDatum
          Pcoarse A.refinement.shading) q).card <= conflictThreshold := by
    intro q
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      (recomputedNeighborhoodActualTubeDatum
        Pcoarse A.refinement.shading)
      hrhoPos hrhoHalf hCfinite hdatumKT q
  have hloss0 :
      ((conflictThreshold + 1 : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero conflictThreshold
  have hlossTop :
      ((conflictThreshold + 1 : Nat) : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdensityBudget :
      ((rho / 8 : NNReal) : ENNReal) ^ etaThird <=
        (eighthNormalizedDatum
          (recomputedNeighborhoodActualTubeDatum
            Pcoarse A.refinement.shading)).shading.shadingDensity /
          ((conflictThreshold + 1 : Nat) : ENNReal) :=
    eighthNormalized_recomputedNeighborhood_densityBudget
      Pcoarse Y A hfine hcoarseIndices htauPos hrhoPos hrhoHalf
      (eta := etaThird)
      (selectionLoss :=
        ((conflictThreshold + 1 : Nat) : ENNReal))
      hloss0 hlossTop hdensityScalar
  have hdeltaRho : delta <= rho := by
    exact (S.delta_le_tau W.m).trans hscale
  let G := canonicalBufferedGlobalCover W hE.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hglobalIdentity : G =
      identityRadiusScaleCover E.family rho hdeltaRho := by
    simpa only [G, rho, C, S] using
      identityCore_canonicalBufferedGlobalCover_eq_identityRadiusScaleCover
        E hE S P W hepsilonHalf
  have hcardScaleU0G :
      (Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover.activeCoarseCardScaleMass
          U0 : ENNReal) =
        (Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover.activeCoarseCardScaleMass
          G : ENNReal) := by
    rfl
  have hCglobal :=
    identitySourceFrostmanKatzTaoConstant_mul_unitBallVolume_le_cardScale
      D hD rho hdeltaRho (eta := etaSource)
  rw [← hglobalIdentity, ← hcardScaleU0G] at hCglobal
  have hX := activeCoarseCardScaleMass_eq_restricted_coarse_card U0
  have hbaseRaw :=
    sourceFrostman_cardScale_to_eighthNormalized_baseBudget
      (X :=
        (Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover.activeCoarseCardScaleMass
          U0 : ENNReal))
      (C := CKT * volume (unitBallBody : Set Space))
      (card := Fintype.card (Fin U.coarseCard))
      (conflictThreshold := conflictThreshold)
      (etaSource := etaSource) (etaThird := etaThird)
      (by simpa only [U] using hX)
      (by simpa only [CKT] using hCglobal)
      hbasePower
  have hbaseBudget :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * CKT) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-etaThird) *
          ((Fintype.card (Fin U.coarseCard) : ENNReal) *
            ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) := by
    simpa only [mul_assoc] using hbaseRaw
  exact
    nonempty_exactOuter_recomputedNeighborhood_coreNativeThirdBundle
      hFthird hbetaTwo Pcoarse Y A hrhoPos hrhoHalf hmass hfrozen hB2
      hconflict hKT hdelta0 hdensityBudget hbaseBudget

#print axioms nonempty_endpointLongCore_identity_exactOuter_recomputedThird

end
end Family8EndpointIdentityExactOuterRecomputedThirdV6
