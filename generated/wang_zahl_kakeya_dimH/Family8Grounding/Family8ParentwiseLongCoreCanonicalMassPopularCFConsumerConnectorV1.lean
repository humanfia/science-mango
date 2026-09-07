import Family8Grounding.Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV2
import Mathlib.Tactic

/-!
# Consumer connector for the canonical parentwise mass-popular CF witness

The high-gamma endpoint used to call the mass-popular selector directly and
unpack its mass, positive-union, and average-product conclusions.  The
parentwise LongCore integration now returns those conclusions in
`MassPopularSelectedParentWithCF`, together with the normalized-CF lower
bound on the old parent represented by the very same selected-fine parent.

This file is deliberately only an elimination bridge.  It neither rebuilds
the restricted cover nor selects a second parent: the output `q` is the
literal `q` stored in the input record, and the cover, shading, and assembly
parameters are unchanged.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ParentwiseLongCoreCanonicalMassPopularCFConsumerConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParentwiseLongCoreCanonicalMassPopularCFV1
open Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV2
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineAssemblyMassPopularV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Project the endpoint consumer's old mass/positivity/product tuple and the
new CF conclusion from one record.  The existential parent is definitionally
`H.q`; in particular this lemma performs no second selection. -/
theorem MassPopularSelectedParentWithCF.exists_endpointConsumerTuple
    {S : StickyScaleCover fine rho} {Y : Shading fine.bodyFamily} {r : Real}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (toConvexFactorization S) Y r}
    {lower : ENNReal}
    (H : MassPopularSelectedParentWithCF S Y r A lower) :
    exists q : {q // q ∈
        (selectedFineScaleCover S A.refinement.indices
          (assembly_indices_subset_activeFine S Y r A)).activeCoarse},
      exists hqOld :
          selectedFineOldParent S A.refinement.indices q.1 ∈ S.activeCoarse,
        (sourceActiveFineShading
            (toConvexFactorization S) Y).shadingMass <=
            (A.loss : ENNReal) * (S.activeCoarse.card : ENNReal) *
              (stickyFiberSourceShading
                (selectedFineScaleCover S A.refinement.indices
                  (assembly_indices_subset_activeFine S Y r A))
                (selectedFineShading
                  S A.refinement.indices A.refinement.shading)
                q.1).shadingMass /\
        0 < volume
          (stickyFiberSourceShading
            (selectedFineScaleCover S A.refinement.indices
              (assembly_indices_subset_activeFine S Y r A))
            (selectedFineShading S A.refinement.indices A.refinement.shading)
            q.1).shadedUnion /\
        (actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (stickyFiberSourceShading
              (selectedFineScaleCover S A.refinement.indices
                (assembly_indices_subset_activeFine S Y r A))
              (selectedFineShading
                S A.refinement.indices A.refinement.shading)
              q.1).averageMultiplicity) /\
        lower <= parentNormalizedFiberCFAt S
          ⟨selectedFineOldParent S A.refinement.indices q.1, hqOld⟩ := by
  exact ⟨H.q, H.oldParent_active, H.source_mass, H.positive_union,
    H.average_product, H.cf_lower⟩

variable {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- Endpoint-shaped wrapper around the restricted canonical producer.  Its
first three conclusions have exactly the old consumer's shape; the final
conclusion is the parentwise LongCore CF lower bound on that same `q`'s old
parent. -/
theorem exists_canonicalTauActiveRestricted_endpointConsumerTuple
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (hepsilon : 0 <= epsilon)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      D hD C N epsilon hepsilon eta S)
    (hFine : D.family.refinement.refined.Nonempty)
    (hepsilonHalf : epsilon <= 1 / 2) :
    let W := Wparent.toNormalizedLongIntervalCoreWitness
      D hD C S hepsilon hFine
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    let lower : ENNReal :=
      (((canonicalBufferedRadius W / S.tau W.m : NNReal) : ENNReal) ^
        eta W.stage)
    forall (Y : Shading (activeFineRestrictedFamily U0).bodyFamily)
      (r : Real)
      (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (toConvexFactorization U) Y r),
      (IndexedShadingRefinement.restrictTo Y U.activeFine).shading.shadingMass
          ≠ 0 ->
        exists q : {q // q ∈
            (selectedFineScaleCover U A.refinement.indices
              (assembly_indices_subset_activeFine U Y r A)).activeCoarse},
          exists hqOld :
              selectedFineOldParent U A.refinement.indices q.1 ∈
                U.activeCoarse,
            (sourceActiveFineShading
                (toConvexFactorization U) Y).shadingMass <=
                (A.loss : ENNReal) * (U.activeCoarse.card : ENNReal) *
                  (stickyFiberSourceShading
                    (selectedFineScaleCover U A.refinement.indices
                      (assembly_indices_subset_activeFine U Y r A))
                    (selectedFineShading
                      U A.refinement.indices A.refinement.shading)
                    q.1).shadingMass /\
            0 < volume
              (stickyFiberSourceShading
                (selectedFineScaleCover U A.refinement.indices
                  (assembly_indices_subset_activeFine U Y r A))
                (selectedFineShading
                  U A.refinement.indices A.refinement.shading)
                q.1).shadedUnion /\
            (actualRefinementShading A).averageMultiplicity <=
              4 * (A.frozenCoarse.averageMultiplicity *
                (stickyFiberSourceShading
                  (selectedFineScaleCover U A.refinement.indices
                    (assembly_indices_subset_activeFine U Y r A))
                  (selectedFineShading
                    U A.refinement.indices A.refinement.shading)
                  q.1).averageMultiplicity) /\
            lower <= parentNormalizedFiberCFAt U
              ⟨selectedFineOldParent U A.refinement.indices q.1,
                hqOld⟩ := by
  dsimp only
  intro Y r A hsource
  obtain ⟨H⟩ :=
    exists_canonicalTauActiveRestricted_massPopularSelectedParentWithCF
      D hD C S hepsilon Wparent hFine hepsilonHalf Y r A hsource
  exact Family8ParentwiseLongCoreCanonicalMassPopularCFConsumerConnectorV1.MassPopularSelectedParentWithCF.exists_endpointConsumerTuple H

#print axioms
  MassPopularSelectedParentWithCF.exists_endpointConsumerTuple
#print axioms
  exists_canonicalTauActiveRestricted_endpointConsumerTuple

end
end Family8ParentwiseLongCoreCanonicalMassPopularCFConsumerConnectorV1
