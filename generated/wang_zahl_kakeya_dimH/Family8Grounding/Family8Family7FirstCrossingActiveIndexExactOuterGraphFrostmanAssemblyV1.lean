import Family8Grounding.Family8Family7CoordinateToVerticalTubeTransportV1
import Family8Grounding.Family8Family7FirstCrossingActiveIndexBufferedFiberFrostmanV3
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketFrostmanV12
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8StickyActiveIndexExactOuterComparableAssemblyV2
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Family8Grounding.Family8StickySourceMassFactorizationRoundTripV1
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection

/-!
# An exact-outer FirstCrossing graph-Frostman assembly on genuine active index types

V1 is frozen with the failed restricted-fibre ancestry.  This successor uses
the clean active buffered fibre transport V2 and otherwise retains the same
assembly, parent, graph, density, product, and Frostman certificate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingActiveIndexExactOuterGraphFrostmanAssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family6AffineConvexVolumeCoreV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7FirstCrossingActiveIndexBufferedFiberFrostmanV3
open Family8Family7FirstCrossingActiveIndexBufferedFiberFrostmanV3.FirstActualNormalizedCrossingWitness
open Family8Family7FirstCrossingFamilyGraphBucketFrostmanV12
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FirstActualCrossingNormalizedFrostmanV2
open Family8FirstActualCrossingNormalizedFrostmanV2.FirstActualNormalizedCrossingWitness
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyActiveIndexExactOuterComparableAssemblyV2
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

/-- The active-index source assembly and a same-fibre FirstCrossing graph
carry mass retention, density, same-assembly product, and Frostman control.
The graph subset is stated on the literal active-restricted cover fibre. -/
theorem exists_activeIndex_firstCrossing_familyGraphBucket_frostman
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (Y : Shading (bufferedLowerFamily D C S W.m).bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        (bufferedIntervalCover
          D hD C S epsilon hepsilon W.m W.rho W.buffered).activeFine).shading.shadingMass ≠ 0)
    (r : Real) (hr : 0 < r) :
    let U := bufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered
    let T := activeFineRestrictedScaleCover U
    let hscale : S.tau W.m ≤ W.rho :=
      actualDatum_tau_le_of_isBuffered
        D hD S hepsilon W.m W.rho W.buffered
    let YR := activeFineRestrictedShading U Y
    let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
    let P := (sourceMassCoarseTubePartition
      T hscale YR hsourceR).asConvexFactorization
    let frostmanC : ENNReal :=
      (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)
    ∃ A : Assembly P YR r,
      A.loss = frozenComparableLoss {i // i ∈ U.activeFine}
        (Fin U.activeCoarse.card) ∧
      (activeFineShading U Y).averageMultiplicity ≤
        (frozenComparableLoss {i // i ∈ U.activeFine}
          (Fin U.activeCoarse.card) : ENNReal) *
          (actualRefinementShading A).averageMultiplicity ∧
      A.frozenCoarse = P.inducedShading A.refinement.shading ∧
      ∃ k ∈ P.index.coarse, ∃ axis : Fin 3, ∃ label : Int,
        let VS := firstCrossingFamilyVerticalSource axis
          (activeFineRestrictedFamily U) P k
        let graph := verticalSourceGraphCBucketFiber
          (((S.tau W.m : NNReal) : Real) / 2) VS label
        let baseLoss : ENNReal :=
          (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
        let d : ENNReal :=
          (sourceActiveFineShading P YR).shadingDensity / baseLoss
        let graphLoss : ENNReal :=
          ((3 * verticalGraphCBucketLoss
            (((S.tau W.m : NNReal) : Real) / 2) : Nat) : ENNReal)
        graph ⊆ T.fiber k ∧
        graph.Nonempty ∧
        WithinFactor
          (3 * verticalGraphCBucketLoss
            (((S.tau W.m : NNReal) : Real) / 2))
          (finalFiberShading A k).shadingMass
          (firstCrossingFamilyGraphBucketShading
            axis label (activeFineRestrictedFamily U) P A k).shadingMass ∧
        d / graphLoss ≤
          (selectedCoarseShading
            (firstCrossingFamilyGraphBucketShading
              axis label (activeFineRestrictedFamily U) P A k)
            graph).shadingDensity ∧
        (firstCrossingFamilyGraphBucketShading
          axis label (activeFineRestrictedFamily U) P A k).shadingMass ≠ 0 ∧
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) ∧
        IsFrostmanOn (frostmanC * (d⁻¹ * graphLoss))
          VS.family.bodyFamily graph
          (affineImageConvexBody
            (coordinateToVerticalRigidMotion axis).toAffineEquiv
            (T.coarse.tubes k).body) := by
  dsimp only
  let U := bufferedIntervalCover
    D hD C S epsilon hepsilon W.m W.rho W.buffered
  let T := activeFineRestrictedScaleCover U
  let hscale : S.tau W.m ≤ W.rho :=
    actualDatum_tau_le_of_isBuffered
      D hD S hepsilon W.m W.rho W.buffered
  let YR := activeFineRestrictedShading U Y
  let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
  let P := (sourceMassCoarseTubePartition
    T hscale YR hsourceR).asConvexFactorization
  let frostmanC : ENNReal :=
    (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)
  obtain ⟨A, hloss, havg, hExactOuter, _k0, _hpositive0, _hproduct0⟩ :=
    exists_activeIndex_exactOuterComparableAssembly
      U hscale Y r hr hsource
  have hround : P = toConvexFactorization T := by
    exact sourceMass_asConvexFactorization_eq_toConvexFactorization
      T hscale YR hsourceR
  have hsourceP :
      (IndexedShadingRefinement.restrictTo YR
        P.index.fine).shading.shadingMass ≠ 0 := by
    rw [hround, toConvexFactorization_fine]
    exact hsourceR
  have hfull := activeIndex_sourceMassFactorization_fibers_isFrostmanOn
    D hD C S epsilon hepsilon eta N W Y hsource
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  obtain ⟨k, hk, axis, label, hgraph⟩ :=
    exists_massPopular_familyGraphBucket_frostman_sameProduct_retained
      (activeFineRestrictedFamily U) P A
      (fun q ↦ (T.coarse.tubes q).body) frostmanC
      hfull htau hsourceP
  refine ⟨A, hloss, havg, hExactOuter, k, hk, axis, label, ?_⟩
  dsimp only at hgraph ⊢
  let VS := firstCrossingFamilyVerticalSource axis
    (activeFineRestrictedFamily U) P k
  let graph := verticalSourceGraphCBucketFiber
    (((S.tau W.m : NNReal) : Real) / 2) VS label
  have hgraphP : graph ⊆ P.index.fiber k := by
    simpa only [graph, VS] using
      firstCrossingFamilyGraphBucket_subset_fiber axis label
        (activeFineRestrictedFamily U) P k
  have hgraphT : graph ⊆ T.fiber k := by
    rw [hround, toConvexFactorization_fiber] at hgraphP
    exact hgraphP
  exact ⟨hgraphT, hgraph⟩

#print axioms
  exists_activeIndex_firstCrossing_familyGraphBucket_frostman

end
end Family8Family7FirstCrossingActiveIndexExactOuterGraphFrostmanAssemblyV1
