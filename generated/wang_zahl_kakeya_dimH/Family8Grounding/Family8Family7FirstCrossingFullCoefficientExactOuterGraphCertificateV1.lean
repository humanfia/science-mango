import Family8Grounding.Family8Family7FirstCrossingActiveIndexExactOuterGraphFrostmanAssemblyV1
import Family8Grounding.Family8Family7FirstCrossingFullCoefficientGraphCertificateV4

/-!
# Exact-outer Family7 full-coefficient graph certificate

The existing certificate structure is reused verbatim.  This successor only
changes its producer to the exact-outer active-index assembly and carries the
literal induced-outer equality alongside the same `A/k/axis/label/graph`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFullCoefficientExactOuterGraphCertificateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family6AffineConvexVolumeCoreV1
open Family8Family7CoordinateGraphGeneralAmbientKatzTaoV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7CoordinateTubeAmbientVolumeV2
open Family8Family7FirstCrossingActiveIndexExactOuterGraphFrostmanAssemblyV1
open Family8Family7FirstCrossingActiveIndexGraphFrostmanConstantFiniteV5
open Family8Family7FirstCrossingBufferedLowerActiveB2SupportV7
open Family8Family7FirstCrossingFamilyGraphBucketAverageRetentionV11
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

/-- The exact-outer active-index Family7 assembly produces the existing
full-coefficient graph certificate without changing the selected graph. -/
theorem exists_activeIndex_firstCrossing_fullCoefficientExactOuterGraphCertificate
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
    (r : Real) (hr : 0 < r)
    (htauSixteenth : S.tau W.m ≤ (1 / 16 : NNReal)) :
    let U := bufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered
    let T := activeFineRestrictedScaleCover U
    let F := activeFineRestrictedFamily U
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
        let baseLoss : ENNReal :=
          (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
        let d : ENNReal :=
          (sourceActiveFineShading P YR).shadingDensity / baseLoss
        let graphLoss : ENNReal :=
          ((3 * verticalGraphCBucketLoss
            (((S.tau W.m : NNReal) : Real) / 2) : Nat) : ENNReal)
        let CF : ENNReal := frostmanC * (d⁻¹ * graphLoss)
        Nonempty
          (FirstCrossingFullCoefficientGraphCertificate
            F T P YR A k axis label CF d graphLoss) := by
  dsimp only
  let U := bufferedIntervalCover
    D hD C S epsilon hepsilon W.m W.rho W.buffered
  let T := activeFineRestrictedScaleCover U
  let F := activeFineRestrictedFamily U
  let hscale : S.tau W.m ≤ W.rho :=
    actualDatum_tau_le_of_isBuffered
      D hD S hepsilon W.m W.rho W.buffered
  let YR := activeFineRestrictedShading U Y
  let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
  let P := (sourceMassCoarseTubePartition
    T hscale YR hsourceR).asConvexFactorization
  let frostmanC : ENNReal :=
    (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)
  obtain ⟨A, hloss, hsourceAverage, hExactOuter,
      k, hk, axis, label, hmain⟩ :=
    exists_activeIndex_firstCrossing_familyGraphBucket_frostman
      D hD C S epsilon hepsilon eta N W Y hsource r hr
  refine ⟨A, hloss, hsourceAverage, hExactOuter,
    k, hk, axis, label, ?_⟩
  dsimp only at hmain ⊢
  let VS := firstCrossingFamilyVerticalSource axis F P k
  let graph := verticalSourceGraphCBucketFiber
    (((S.tau W.m : NNReal) : Real) / 2) VS label
  let baseLoss : ENNReal :=
    (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
  let d : ENNReal :=
    (sourceActiveFineShading P YR).shadingDensity / baseLoss
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss
      (((S.tau W.m : NNReal) : Real) / 2) : Nat) : ENNReal)
  let verticalAmbient : ConvexBody Space :=
    affineImageConvexBody
      (coordinateToVerticalRigidMotion axis).toAffineEquiv
      (T.coarse.tubes k).body
  let CF : ENNReal := frostmanC * (d⁻¹ * graphLoss)
  rcases hmain with
    ⟨hgraphT, hgraphNonempty, hretained, hdensity, hgraphMass,
      _hpositive, hproduct, hgraphFrostman⟩
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < W.rho := htau.trans_le hscale
  have hround : P = toConvexFactorization T := by
    exact sourceMass_asConvexFactorization_eq_toConvexFactorization
      T hscale YR hsourceR
  have hsourceP :
      (IndexedShadingRefinement.restrictTo YR
        P.index.fine).shading.shadingMass ≠ 0 := by
    rw [hround, toConvexFactorization_fine]
    exact hsourceR
  have hCFfinite : CF ≠ ∞ := by
    simpa only [baseLoss, d, graphLoss, frostmanC, CF] using
      firstCrossing_graphFrostmanConstant_ne_top_of_sourceMass
        D hD C S epsilon hepsilon eta N W F P YR A k hk hsourceP
  have hcoordinateFrostman : IsFrostmanOn CF
      (coordinateToVerticalFamily axis F).bodyFamily graph
      verticalAmbient := by
    simpa only [VS, graph, F, P, verticalAmbient, CF,
      firstCrossingFamilyVerticalSource,
      coordinateToVerticalChartSourceV2] using hgraphFrostman
  have hvertical0 : volume (verticalAmbient : Set Space) ≠ 0 := by
    simpa only [verticalAmbient] using
      coordinateTubeAmbient_volume_ne_zero axis (T.coarse.tubes k) hrho
  have hverticalTop : volume (verticalAmbient : Set Space) ≠ ∞ := by
    simpa only [verticalAmbient] using
      coordinateTubeAmbient_volume_ne_top axis (T.coarse.tubes k)
  let Cgraph := coordinateGraphGeneralAmbientKatzTaoConstant
    axis F graph verticalAmbient CF
  have hCgraphFinite : Cgraph ≠ ∞ := by
    exact coordinateGraphGeneralAmbientKatzTaoConstant_ne_top
      axis F graph verticalAmbient hCFfinite hvertical0
  have hsourceKT : IsKatzTao Cgraph
      (activeSubtypeFamily F.bodyFamily graph) := by
    exact sourceGraph_isKatzTao_of_coordinate_isFrostmanOn_generalAmbient
      axis F graph verticalAmbient hvertical0 hverticalTop
        hcoordinateFrostman
  have hfinalAverage : (finalFiberShading A k).averageMultiplicity ≤
      graphLoss *
        (firstCrossingFamilyGraphBucketShading
          axis label F P A k).averageMultiplicity := by
    simpa only [graphLoss] using
      finalFiber_averageMultiplicity_le_graphLoss_mul_graphAverage
        axis label F P A k hretained
  have hB2 : ∀ i, i ∈ graph →
      (VS.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2 := by
    intro i _hi
    change (((coordinateToVerticalFamily axis
      (bufferedLowerFamily D C S W.m)).tubes i.1).carrier) ⊆
        Metric.closedBall (0 : Space) 2
    exact
      coordinateToVertical_bufferedLowerFamily_activeFine_carrier_subset_closedBall_two
        D hD C S epsilon hepsilon W.m W.rho W.buffered
          htauSixteenth axis i.1 i.2
  change Nonempty
    (FirstCrossingFullCoefficientGraphCertificate
      F T P YR A k axis label CF d graphLoss)
  refine Nonempty.intro
    { graph_subset := by simpa only [graph, VS] using hgraphT
      graph_nonempty := by simpa only [graph, VS] using hgraphNonempty
      graph_density := by simpa only [graph, VS] using hdensity
      graph_mass_ne_zero := hgraphMass
      final_average := hfinalAverage
      same_product := hproduct
      graph_katz_tao_constant_finite := by
        simpa only [fullCoefficientGraphKatzTaoConstant,
          graph, VS, verticalAmbient, Cgraph] using hCgraphFinite
      graph_katz_tao := by
        simpa only [fullCoefficientGraphKatzTaoConstant,
          graph, VS, verticalAmbient, Cgraph] using hsourceKT
      vertical_b2 := by simpa only [graph, VS] using hB2 }

#print axioms
  exists_activeIndex_firstCrossing_fullCoefficientExactOuterGraphCertificate

end
end Family8Family7FirstCrossingFullCoefficientExactOuterGraphCertificateV1
