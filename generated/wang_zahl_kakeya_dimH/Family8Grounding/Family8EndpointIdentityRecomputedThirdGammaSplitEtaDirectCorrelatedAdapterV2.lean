import Family8Grounding.Family8EndpointIdentityExactOuterRecomputedThirdDirectCorrelatedV7

/-!
# Endpoint recomputed third with split source and third exponents

The source Frostman--Katz--Tao constant and the native recomputed third do
not need the same loss exponent.  This module keeps a smaller `outputEta` on
the literal source datum and a larger `thirdEta` on the Frostman theorem used
by the recomputed third.  The density and base gates therefore gain the
honest interval between these two exponents.

This is an object-preserving adapter to the already verified generic exact
outer theorem.  It introduces no new geometric or scalar conclusion.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityRecomputedThirdGammaSplitEtaDirectCorrelatedAdapterV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EndpointIdentityExactOuterRecomputedThirdDirectCorrelatedV7
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8FullRefinementActualDatumV1
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
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


/-- Gamma-native recomputed-third production with independent source and
third loss exponents.  The literal source constant is built at `outputEta`;
the normalized density and base gates, as well as the exact Frostman theorem
for the new third datum, use `thirdEta`. -/
theorem nonempty_endpointLongCore_identity_exactOuter_recomputedThird_gamma_splitEta_directCorrelated
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
    (targetEpsilon outputEta thirdEta : Real) (delta0 : NNReal)
    (hFOutput : FrostmanHypotheses D outputEta)
    (hFExact : FrostmanAtParameters
      gamma (targetEpsilon / 4) thirdEta delta0)
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
        Family8IdentityCoreTauActiveSingletonFiberV4.identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          E hE S W P.epsilon_pos.le hepsilonHalf k
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse 1 hM
    let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    forall A : Assembly Pcoarse.asConvexFactorization Y 1,
      A.frozenCoarse =
          Pcoarse.asConvexFactorization.inducedShading
            A.refinement.shading ->
      (((rho / 8 : NNReal) : ENNReal) ^ thirdEta *
          (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
        Y.shadingDensity ^ 2 /
          ((A.loss : ENNReal) *
            (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2))) ->
      (((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * CKT) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-thirdEta) *
          ((Fintype.card (Fin U.coarseCard) : ENNReal) *
            ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2))) ->
      Nonempty
        (CoreNativeFrozenThirdBundle
          Pcoarse.asConvexFactorization Y A rho
          (eighthSelectedThirdFactorLoss rho
            ((432 : ENNReal) *
              ((conflictThreshold + 1 : Nat) : ENNReal))
            (targetEpsilon / 4) gamma)
          gamma) := by
  exact
    nonempty_endpointLongCore_identity_exactOuter_recomputedThird_directCorrelated
      D hD P W hepsilonHalf hbufferedSixteenth
      (etaSource := outputEta)
      (etaThird := thirdEta)
      (epsilonThird := targetEpsilon / 4)
      (betaThird := gamma)
      (delta0 := delta0)
      hFOutput hFExact hgammaTwo hdelta0

#print axioms
  nonempty_endpointLongCore_identity_exactOuter_recomputedThird_gamma_splitEta_directCorrelated

end
end Family8EndpointIdentityRecomputedThirdGammaSplitEtaDirectCorrelatedAdapterV2
