import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8Family7FirstCrossingExactOuterIdentitySingletonMiddleV6
import Family8Grounding.Family8IdentityCoreTauActiveSingletonFiberV4
import Family8Grounding.Family8NormalizedLongCoreTauActiveBasicTransportsV2
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import Mathlib.Tactic

/-!
# Endpoint identity loss-free triple on one frozen graph assembly

The graph certificate stored by `SameAssemblyFullCoefficientGraphIdentity`
already contains the same-product inequality on its literal assembly.  At
the endpoint identity cover, every parent fibre has cardinality at most one.
This file combines those two facts with the exact endpoint source-average
identity.  No exact-outer field, graph-bucket loss, proxy, or new selection is
used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalGraphFrozenEndpointIdentityLossFreeTripleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8Family7FirstCrossingExactOuterIdentitySingletonMiddleV6
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8SourceActiveFineActualAverageIdentityV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberFactorizationRoundTripV2
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- On the endpoint identity cover, any graph identity whose factorization is
the literal scale-cover factorization satisfies the loss-free same-assembly
triple.  The graph certificate is used only for its `same_product` field;
the selected graph itself never enters the estimate. -/
theorem endpointIdentity_sameR_lossFreeTriple
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    forall (Q : ConvexFactorization
        (activeFineRestrictedFamily U0).bodyFamily U.coarse.bodyFamily),
      Q = toConvexFactorization U ->
      forall (fibreCF : ENNReal),
      forall R : SameAssemblyFullCoefficientGraphIdentity
        (activeFineRestrictedFamily U0) U Q Y fibreCF,
        D.shading.averageMultiplicity <=
          ((R.A.loss : ENNReal) * 4) *
            R.A.frozenCoarse.averageMultiplicity := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  intro Q hQ
  subst Q
  intro fibreCF R
  let cert := Classical.choice R.graphCertificate
  have hfine : (toConvexFactorization U).index.fine = Finset.univ := by
    rw [toConvexFactorization_fine]
    exact activeFineRestrictedScaleCover_activeFine U0
  have hsourceEq :
      (IndexedShadingRefinement.restrictTo Y
        (toConvexFactorization U).index.fine).shading.averageMultiplicity =
          D.shading.averageMultiplicity := by
    rw [hfine, restrictTo_univ_averageMultiplicity]
    calc
      Y.averageMultiplicity =
          (activeFineShading U0 Dtau.shading).averageMultiplicity :=
        activeFineRestrictedShading_averageMultiplicity U0 Dtau.shading
      _ = Dtau.shading.averageMultiplicity :=
        canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
          E hE C S P W hepsilonHalf
      _ = D.shading.averageMultiplicity :=
        endpointLongCore_tauActive_averageMultiplicity_eq_source D hD P W
  have hfiberU : (U.fiber R.k).card <= 1 := by
    simpa only [Fintype.card_coe] using
      (identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf R.k)
  have hfiberQ : ((toConvexFactorization U).index.fiber R.k).card <= 1 := by
    rw [toConvexFactorization_fiber]
    exact hfiberU
  have hfinalCard :=
    finalFiberShading_averageMultiplicity_le_fiberCard
      (activeFineRestrictedFamily U0) U (toConvexFactorization U) Y R.A R.k
  have hcardOne :
      (((toConvexFactorization U).index.fiber R.k).card : ENNReal) <= 1 := by
    exact_mod_cast hfiberQ
  have hfinalOne :
      (finalFiberShading R.A R.k).averageMultiplicity <= 1 :=
    hfinalCard.trans hcardOne
  have hsource :=
    restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement R.A
  calc
    D.shading.averageMultiplicity =
        (IndexedShadingRefinement.restrictTo Y
          (toConvexFactorization U).index.fine).shading.averageMultiplicity :=
      hsourceEq.symm
    _ <= (R.A.loss : ENNReal) *
        (actualRefinementShading R.A).averageMultiplicity := hsource
    _ <= (R.A.loss : ENNReal) *
        (4 * (R.A.frozenCoarse.averageMultiplicity *
          (finalFiberShading R.A R.k).averageMultiplicity)) :=
      mul_le_mul' le_rfl cert.same_product
    _ <= (R.A.loss : ENNReal) *
        (4 * (R.A.frozenCoarse.averageMultiplicity * 1)) :=
      mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl hfinalOne))
    _ = ((R.A.loss : ENNReal) * 4) *
        R.A.frozenCoarse.averageMultiplicity := by
      ac_rfl

/-- The exact specialization used by the gamma-native graph producer.  Its
bounded-fibre partition forgets definitionally to the scale-cover
factorization, so the preceding theorem applies without transporting or
reselecting the graph identity. -/
theorem endpointIdentity_boundedFiberSameR_lossFreeTriple
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    forall (M : Nat),
    forall (hM : forall k, k ∈ U.activeCoarse ->
      (U.fiber k).card <= M),
    forall (hcoarse : U.activeCoarse.Nonempty),
      let Pcoarse := boundedFiberCoarseTubePartition U
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
        hcoarse M hM
      forall (fibreCF : ENNReal),
      forall R : SameAssemblyFullCoefficientGraphIdentity
        (activeFineRestrictedFamily U0) U
          Pcoarse.asConvexFactorization Y fibreCF,
        D.shading.averageMultiplicity <=
          ((R.A.loss : ENNReal) * 4) *
            R.A.frozenCoarse.averageMultiplicity := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  intro M hM hcoarse
  let hscale : S.tau W.m <= canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Pcoarse := boundedFiberCoarseTubePartition U hscale hcoarse M hM
  intro fibreCF R
  exact endpointIdentity_sameR_lossFreeTriple D hD P W hepsilonHalf
    Pcoarse.asConvexFactorization
      (boundedFiber_asConvexFactorization_eq_toConvexFactorization
        U hscale hcoarse M hM)
    fibreCF R

#print axioms endpointIdentity_sameR_lossFreeTriple
#print axioms endpointIdentity_boundedFiberSameR_lossFreeTriple

end
end Family8CanonicalGraphFrozenEndpointIdentityLossFreeTripleV1
