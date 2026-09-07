import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Family8Grounding.Family8IdentityCoreTauActiveSingletonFiberV4
import Family8Grounding.Family8NormalizedLongCoreTauActiveBasicTransportsV2
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Family8Grounding.Family8StickyBoundedFiberPartitionFineIndexV3
import Mathlib.Tactic

/-!
# Loss-free endpoint raw product on the canonical same graph

At the identity endpoint every lower-to-buffered fibre is a singleton.  The
full-coefficient graph certificate already retains the same assembly product,
so its graph-bucket estimate is unnecessary for the raw three-factor product:
the final-fibre average is at most one.  This module combines that observation
with the exact endpoint source-average transport on the literal bounded
factorization used by the gamma-native third-first producer.

In particular, the conclusion contains neither the vertical graph-bucket loss
nor a proxy-density/Frostman premise.  The assembly, frozen coarse shading and
graph identity are exactly those stored in the supplied `R`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenEndpointLossFreeSameRRawEq66V1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8FrostmanOneFromPointwisePackingV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberFactorizationRoundTripV2
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberPartitionFineIndexV3
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8SourceActiveFineActualAverageIdentityV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- The final shading in one factorization fibre has average multiplicity at
most the cardinality of that literal fibre. -/
theorem finalFiberShading_averageMultiplicity_le_fiberCard
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (Q : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y r)
    (k : Fin T.coarseCard) :
    (finalFiberShading A k).averageMultiplicity <=
      ((Q.index.fiber k).card : ENNReal) := by
  apply averageMultiplicity_le_natCap_of_pointwise_le
  intro x
  rw [finalFiberShading_pointMultiplicity]
  exact
    Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly.fiberMultiplicity_le_fiber_card
      Q A.refinement.shading k x

/-- Endpoint identity removes the graph bucket from the raw same-assembly
product.  This is stated for an arbitrary bounded-fibre cap `M`: the bounded
partition is definitionally transported back to the same endpoint cover, whose
actual fibres have cardinality at most one independently of `M`.

The source restriction of `R.A` is the original datum average exactly.  Its
standard loss retention and `R`'s own `same_product` field therefore give the
literal middle count one and middle coefficient `R.A.loss * 4`.
-/
theorem endpointLongCore_identity_sameGraph_lossFour_rawEq66
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {epsilon0 beta gamma : Real}
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
    forall (M : Nat)
      (hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M)
      (hcoarse : U.activeCoarse.Nonempty),
      let Pcoarse := boundedFiberCoarseTubePartition U
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
        hcoarse M hM
      forall (fibreCF : ENNReal)
        (R : SameAssemblyFullCoefficientGraphIdentity
          (activeFineRestrictedFamily U0) U
          Pcoarse.asConvexFactorization Y fibreCF),
        D.shading.averageMultiplicity <=
          1 * (((R.A.loss : ENNReal) * 4) *
            R.A.frozenCoarse.averageMultiplicity) := by
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
  have hfine :
      Pcoarse.asConvexFactorization.index.fine = U.activeFine := by
    simpa only [Pcoarse, hscale] using
      boundedFiberCoarseTubePartition_asConvexFactorization_fine
        U hscale hcoarse M hM
  have hU : U.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine U0
  have hsourceAverage :
      (IndexedShadingRefinement.restrictTo Y
        Pcoarse.asConvexFactorization.index.fine).shading.averageMultiplicity =
        D.shading.averageMultiplicity := by
    calc
      (IndexedShadingRefinement.restrictTo Y
          Pcoarse.asConvexFactorization.index.fine).shading.averageMultiplicity =
          Y.averageMultiplicity := by
        rw [hfine, hU, restrictTo_univ_averageMultiplicity]
      _ = (activeFineShading U0 Dtau.shading).averageMultiplicity :=
        activeFineRestrictedShading_averageMultiplicity U0 Dtau.shading
      _ = Dtau.shading.averageMultiplicity :=
        canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
          E hE C S P W hepsilonHalf
      _ = D.shading.averageMultiplicity :=
        endpointLongCore_tauActive_averageMultiplicity_eq_source D hD P W
  have hsourceRetention : D.shading.averageMultiplicity <=
      (R.A.loss : ENNReal) *
        (actualRefinementShading R.A).averageMultiplicity := by
    rw [<- hsourceAverage]
    exact restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement
      R.A
  have hfiber : (Pcoarse.asConvexFactorization.index.fiber R.k).card <= 1 := by
    change (U.fiber R.k).card <= 1
    simpa only [U, U0, C, S, E, hE, Fintype.card_coe] using
      (identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf R.k)
  have hfinalCard := finalFiberShading_averageMultiplicity_le_fiberCard
    (activeFineRestrictedFamily U0) U Pcoarse.asConvexFactorization Y R.A R.k
  have hfiberENN :
      ((Pcoarse.asConvexFactorization.index.fiber R.k).card : ENNReal) <= 1 := by
    exact_mod_cast hfiber
  have hfinalOne : (finalFiberShading R.A R.k).averageMultiplicity <= 1 :=
    hfinalCard.trans hfiberENN
  let cert := Classical.choice R.graphCertificate
  calc
    D.shading.averageMultiplicity <=
        (R.A.loss : ENNReal) *
          (actualRefinementShading R.A).averageMultiplicity := hsourceRetention
    _ <= (R.A.loss : ENNReal) *
        (4 * (R.A.frozenCoarse.averageMultiplicity *
          (finalFiberShading R.A R.k).averageMultiplicity)) :=
      mul_le_mul' le_rfl cert.same_product
    _ <= (R.A.loss : ENNReal) *
        (4 * (R.A.frozenCoarse.averageMultiplicity * 1)) :=
      mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl hfinalOne))
    _ = 1 * (((R.A.loss : ENNReal) * 4) *
        R.A.frozenCoarse.averageMultiplicity) := by
      ac_rfl

#print axioms finalFiberShading_averageMultiplicity_le_fiberCard
#print axioms endpointLongCore_identity_sameGraph_lossFour_rawEq66

end
end Family8CanonicalGraphFrozenEndpointLossFreeSameRRawEq66V1
