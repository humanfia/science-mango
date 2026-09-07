import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Family8Grounding.Family8Family7CoordinateGraphGeneralAmbientKatzTaoV1
import Family8Grounding.Family8Family7CoordinateTubeAmbientVolumeV2
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketAverageRetentionV11
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketFrostmanV12
import Family8Grounding.Family8Family7FirstCrossingFullCoefficientGraphCertificateV4

/-!
# Family7 graph certificate from fibre Frostman control, V3

The graph-bucket restriction enlarges the fibre Frostman coefficient by the
literal factor `d⁻¹ * graphLoss`.  This clean adapter records that effective
coefficient in the output certificate.  Earlier drafts attempted to refold
the effective coefficient as the raw fibre coefficient and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FullCoefficientGraphCertificateFromFibreFrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8Family7CoordinateGraphGeneralAmbientKatzTaoV1
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7CoordinateTubeAmbientVolumeV2
open Family8Family7FirstCrossingFamilyGraphBucketAverageRetentionV11
open Family8Family7FirstCrossingFamilyGraphBucketFrostmanV12
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickySourceMassFactorizationRoundTripV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- A factorization-wide literal fibre Frostman certificate selects one
Family7 graph.  The output uses the exact graph-restricted Frostman
coefficient `CF * (d⁻¹ * graphLoss)`. -/
theorem exists_fullCoefficientGraphCertificate_of_fibresFrostman
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) {r : Real} (A : Assembly P Y r)
    (CF : ENNReal) (hCFfinite : CF ≠ ∞)
    (hfull : ∀ q ∈ P.index.coarse,
      IsFrostmanOn CF F.bodyFamily (P.index.fiber q)
        (T.coarse.tubes q).body)
    (htau : 0 < tau) (hrho : 0 < rho)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass ≠ 0)
    (hround : P = toConvexFactorization T)
    (hverticalB2 : ∀ axis : Fin 3, ∀ i ∈ T.activeFine,
      ((coordinateToVerticalFamily axis F).tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 2) :
    ∃ k ∈ P.index.coarse, ∃ axis : Fin 3, ∃ label : Int,
      let baseLoss : ENNReal :=
        (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
      let d : ENNReal :=
        (sourceActiveFineShading P Y).shadingDensity / baseLoss
      let graphLoss : ENNReal :=
        ((3 * verticalGraphCBucketLoss
          ((tau : Real) / 2) : Nat) : ENNReal)
      let effectiveCF : ENNReal := CF * (d⁻¹ * graphLoss)
      Nonempty
        (FirstCrossingFullCoefficientGraphCertificate
          F T P Y A k axis label effectiveCF d graphLoss) := by
  obtain ⟨k, hk, axis, label, hgraph⟩ :=
    exists_massPopular_familyGraphBucket_frostman_sameProduct_retained
      F P A (fun q ↦ (T.coarse.tubes q).body) CF hfull htau hsource
  dsimp only at hgraph ⊢
  let VS := firstCrossingFamilyVerticalSource axis F P k
  let graph := verticalSourceGraphCBucketFiber
    ((tau : Real) / 2) VS label
  let baseLoss : ENNReal :=
    (A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
  let d : ENNReal :=
    (sourceActiveFineShading P Y).shadingDensity / baseLoss
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss
      ((tau : Real) / 2) : Nat) : ENNReal)
  let effectiveCF : ENNReal := CF * (d⁻¹ * graphLoss)
  let verticalAmbient : ConvexBody Space :=
    affineImageConvexBody
      (coordinateToVerticalRigidMotion axis).toAffineEquiv
      (T.coarse.tubes k).body
  rcases hgraph with
    ⟨hgraphNonempty, hretained, hdensity, hgraphMass,
      _hpositive, hproduct, hgraphFrostman⟩
  have hgraphP : graph ⊆ P.index.fiber k := by
    simpa only [graph, VS] using
      firstCrossingFamilyGraphBucket_subset_fiber axis label F P k
  have hgraphT : graph ⊆ T.fiber k := by
    rw [hround, toConvexFactorization_fiber] at hgraphP
    exact hgraphP
  have hsourceMass :
      (sourceActiveFineShading P Y).shadingMass ≠ 0 := by
    rw [sourceActiveFineShading_shadingMass]
    exact hsource
  have hsourceDensity0 :
      (sourceActiveFineShading P Y).shadingDensity ≠ 0 := by
    unfold Shading.shadingDensity
    exact ENNReal.div_ne_zero.mpr
      ⟨hsourceMass, familyVolume_ne_top (sourceActiveFineFamily P)⟩
  have hbaseTop : baseLoss ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top A.loss)
      (ENNReal.natCast_ne_top P.index.coarse.card)
  have hd0 : d ≠ 0 := by
    exact ENNReal.div_ne_zero.mpr ⟨hsourceDensity0, hbaseTop⟩
  have hgraphLossTop : graphLoss ≠ ∞ := by
    exact ENNReal.natCast_ne_top _
  have heffectiveFinite : effectiveCF ≠ ∞ := by
    dsimp only [effectiveCF]
    exact ENNReal.mul_ne_top hCFfinite
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hd0) hgraphLossTop)
  have hcoordinateFrostman : IsFrostmanOn effectiveCF
      (coordinateToVerticalFamily axis F).bodyFamily graph
      verticalAmbient := by
    simpa only [VS, graph, verticalAmbient, effectiveCF,
      firstCrossingFamilyVerticalSource,
      coordinateToVerticalChartSourceV2] using hgraphFrostman
  have hvertical0 : volume (verticalAmbient : Set Space) ≠ 0 := by
    simpa only [verticalAmbient] using
      coordinateTubeAmbient_volume_ne_zero axis (T.coarse.tubes k) hrho
  have hverticalTop : volume (verticalAmbient : Set Space) ≠ ∞ := by
    simpa only [verticalAmbient] using
      coordinateTubeAmbient_volume_ne_top axis (T.coarse.tubes k)
  let Cgraph := coordinateGraphGeneralAmbientKatzTaoConstant
    axis F graph verticalAmbient effectiveCF
  have hCgraphFinite : Cgraph ≠ ∞ := by
    exact coordinateGraphGeneralAmbientKatzTaoConstant_ne_top
      axis F graph verticalAmbient heffectiveFinite hvertical0
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
    intro i hi
    change ((coordinateToVerticalFamily axis F).tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 2
    have hiFine : i ∈ T.activeFine :=
      (T.mem_fiber i k).mp (hgraphT hi) |>.1
    exact hverticalB2 axis i hiFine
  refine ⟨k, hk, axis, label, ?_⟩
  change Nonempty
    (FirstCrossingFullCoefficientGraphCertificate
      F T P Y A k axis label effectiveCF d graphLoss)
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

#print axioms exists_fullCoefficientGraphCertificate_of_fibresFrostman

end
end Family8Family7FullCoefficientGraphCertificateFromFibreFrostmanV3
