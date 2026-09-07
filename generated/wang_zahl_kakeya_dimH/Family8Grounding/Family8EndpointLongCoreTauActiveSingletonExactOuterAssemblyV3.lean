import Family8Grounding.Family8CoarseTubePartitionExactOuterComparableAdapterV1
import Family8Grounding.Family8EndpointLongCoreTauActiveSourceMassIdentityV1
import Family8Grounding.Family8IdentityCoreTauActiveSingletonFiberV4
import Family8Grounding.Family8StickyBoundedFiberPartitionFineIndexV3
import Family8Grounding.Family8StickyKatzTaoBoundedFiberPartitionV4
import Mathlib.Tactic

/-!
# Endpoint identity-core singleton exact-outer assembly, V3

V1 timed out while elaborating the fully dependent theorem boundary at seven
million heartbeats.  V2 is frozen with malformed ASCII notation.  This clean
successor keeps the literal endpoint objects and conclusion unchanged and
gives the declaration a larger local elaboration budget.  It imports neither
predecessor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 28000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactOuterComparableAdapterV1
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberPartitionFineIndexV3
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The literal endpoint singleton partition and one exact-outer assembly,
including the positive final-fibre witness used by the same-object DSO. -/
theorem exists_endpointLongCore_canonicalBufferedTauActive_singletonExactOuterAssembly
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hmass : D.shading.shadingMass ≠ 0) :
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
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
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
    Pcoarse.branchingLoss = 1 /\
      Pcoarse.branching = 1 /\
      ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
          Pcoarse.asConvexFactorization Y 1,
        A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
            (Fin U.coarseCard) /\
        A.frozenCoarse =
          Pcoarse.asConvexFactorization.inducedShading
            A.refinement.shading /\
        ∃ k ∈ Pcoarse.coarseIndices,
          0 < volume (finalFiberShading A k).shadedUnion := by
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
  have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
    rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
      D hD P W hepsilonHalf]
    exact hmass
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
  have hscale : S.tau W.m <= canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  let Pcoarse := boundedFiberCoarseTubePartition U hscale hcoarse 1 hM
  have hfine :
      Pcoarse.asConvexFactorization.index.fine = U.activeFine := by
    simpa only [Pcoarse] using
      boundedFiberCoarseTubePartition_asConvexFactorization_fine
        U hscale hcoarse 1 hM
  have hsourceP :
      (IndexedShadingRefinement.restrictTo Y
        Pcoarse.fineIndices).shading.shadingMass ≠ 0 := by
    change (IndexedShadingRefinement.restrictTo Y
      Pcoarse.asConvexFactorization.index.fine).shading.shadingMass ≠ 0
    rw [hfine]
    exact hsource
  obtain ⟨A, hLoss, _hfiberLabel, _houterLabel, hfrozen,
      _hmassRetention, _hdensityRetention, k, hk, hpositive,
      _hfiberLower, _hfiberUpper, _houterLower, _houterUpper, _hproduct⟩ :=
    exists_exactOuter_frozenComparableAssembly_of_coarseTubePartition
      Pcoarse Y 1 (by norm_num) hsourceP
  refine ⟨?_, ?_, A, ?_, hfrozen, k, hk, hpositive⟩
  · exact boundedFiberCoarseTubePartition_branchingLoss
      U hscale hcoarse 1 hM
  · exact boundedFiberCoarseTubePartition_branching
      U hscale hcoarse 1 hM
  · simpa only [U, Y, Pcoarse] using hLoss

#print axioms
  exists_endpointLongCore_canonicalBufferedTauActive_singletonExactOuterAssembly

end
end Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
