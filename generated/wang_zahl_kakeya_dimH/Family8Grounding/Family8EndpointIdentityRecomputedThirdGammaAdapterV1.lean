import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8EndpointIdentityExactOuterRecomputedThirdV6
import Family8Grounding.Family8SectionEightOutputEtaV1

/-!
# Endpoint identity recomputed-third gamma adapter

The generic exact-outer theorem permits an independent exponent on its
native third bundle.  At the canonical output-eta boundary, instantiate that
exponent with `gamma` itself and use the exact Frostman input at
`targetEpsilon / 4`.  Consequently the result is already a gamma-native
bundle: no beta-to-gamma refold and no fourth-card-scale gate are needed.

The density and base-power inequalities below remain explicit.  They are
the two genuine scalar gates consumed by the generic recomputed-third
theorem; this adapter does not manufacture either one.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityRecomputedThirdGammaAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFineRestrictedCardScaleMassRefoldV3
open Family8AllFrostmanStickyUnionProducerV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8CoreNativeFrozenThirdBundleV1
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EndpointIdentityExactOuterRecomputedThirdV6
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8ExactOuterRecomputedNeighborhoodCoreNativeThirdBundleV2
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8FrozenNeighborhoodAssemblyV1
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
open Family8SectionEightOutputEtaV1
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

/-- Gamma-native specialization of the endpoint recomputed-third theorem.

`hFOutput` controls the source side at the smaller output exponent, whereas
`hFExact` is used only for the native third factor at exponent `gamma` and
loss `targetEpsilon / 4`.  The first Frostman input also implies the nonzero
source mass needed by the generic theorem.  The final two arrows are the
honest density (`G1`) and base-power (`G2`) gates. -/
theorem nonempty_endpointLongCore_identity_exactOuter_recomputedThird_gamma
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
    (targetEpsilon sourceEta : Real) (delta0 : NNReal)
    (hFOutput : FrostmanHypotheses D
      (sectionEightOutputEta P sourceEta))
    (hFExact : FrostmanAtParameters
      gamma (targetEpsilon / 4) sourceEta delta0)
    (hgammaTwo : gamma <= 2)
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
      have hmass : D.shading.shadingMass ≠ 0 := by
        have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
          D hD hFOutput
        exact ne_of_gt ((ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hD.delta_pos)
          ENNReal.coe_ne_top).trans_le hfloor)
      have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
        rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf]
        exact hmass
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
    let CKT := identitySourceFrostmanKatzTaoConstant D rho
      (sectionEightOutputEta P sourceEta)
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    forall A : Assembly Pcoarse.asConvexFactorization Y 1,
      A.frozenCoarse =
          Pcoarse.asConvexFactorization.inducedShading
            A.refinement.shading ->
      (((rho / 8 : NNReal) : ENNReal) ^ sourceEta *
          (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
        Y.shadingDensity ^ 2 /
          ((A.loss : ENNReal) *
            (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2))) ->
      (((conflictThreshold + 1 : Nat) : ENNReal) * 2097152 *
          (delta : ENNReal) ^
            (-(sectionEightOutputEta P sourceEta)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-sourceEta)) ->
      Nonempty
        (CoreNativeFrozenThirdBundle
          Pcoarse.asConvexFactorization Y A rho
          (eighthSelectedThirdFactorLoss rho
            ((432 : ENNReal) *
              ((conflictThreshold + 1 : Nat) : ENNReal))
            (targetEpsilon / 4) gamma)
          gamma) := by
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
      D hD hFOutput
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos)
      ENNReal.coe_ne_top).trans_le hfloor)
  exact
    nonempty_endpointLongCore_identity_exactOuter_recomputedThird
      D hD P W hepsilonHalf hbufferedSixteenth hmass
      (etaSource := sectionEightOutputEta P sourceEta)
      (etaThird := sourceEta)
      (epsilonThird := targetEpsilon / 4)
      (betaThird := gamma)
      (delta0 := delta0)
      hFOutput hFExact hgammaTwo hdelta0

#print axioms
  nonempty_endpointLongCore_identity_exactOuter_recomputedThird_gamma

end
end Family8EndpointIdentityRecomputedThirdGammaAdapterV1
