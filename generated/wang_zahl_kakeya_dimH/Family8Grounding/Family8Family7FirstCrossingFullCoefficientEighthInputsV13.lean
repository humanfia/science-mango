import Family8Grounding.Family8EighthNormalizedActiveKatzTaoFrostmanV4
import Family8Grounding.Family8EighthNormalizedWZL3SourceV3
import Family8Grounding.Family8Family7CoordinateToVerticalFamilyV1
import Family8Grounding.Family8Family7CoordinateToVerticalSelectedSubtypeKatzTaoForwardV1
import Family8Grounding.Family8Family7CoordinateToVerticalWeightedChartSourceV2
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketV12
import Family8Grounding.Family8FullCoefficientActualMassProxyAverageV10
import Family8Grounding.Family8FullCoefficientEighthNormalizedActiveAverageV10

/-!
# Same-graph inputs for the eighth-normalized full-coefficient branch, V13

This clean successor makes both coordinate-family owners explicit and uses
pointwise family equalities for the vertical and eighth-normalized transports,
while preserving the literal graph and all conclusions.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFullCoefficientEighthInputsV13

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EighthNormalizedActiveKatzTaoFrostmanV4
open Family8EighthNormalizedWZL3SourceV3
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalSelectedSubtypeKatzTaoForwardV1
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FullCoefficientActualMassProxyAverageV10
open Family8FullCoefficientEighthNormalizedActiveAverageV10
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1

noncomputable section

universe v

/-- The exact vertical source datum whose active graph is normalized by the
full-coefficient branch. -/
def firstCrossingVerticalGraphSourceDatum
    {radius : NNReal} {iota : Type} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    {coarseFamily : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarseFamily)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) : ActualTubeDatum radius iota where
  family := (firstCrossingFamilyVerticalSource axis F P k).family
  shading := firstCrossingFamilyVerticalShading axis F P A k

/-- All non-scalar full-coefficient inputs on one literal Family7 graph. -/
theorem firstCrossingGraph_fullCoefficientEighth_inputs
    {radius : NNReal} {iota : Type} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarseFamily : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarseFamily)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hradius : 0 < radius)
    (hradiusHalf : radius ≤ (2 : NNReal)⁻¹)
    (hgraphNonempty :
      (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFamilyVerticalSource axis F P k) label).Nonempty)
    (hB2 : let VS := firstCrossingFamilyVerticalSource axis F P k
      let graph := verticalSourceGraphCBucketFiber
        ((radius : Real) / 2) VS label
      ∀ i, i ∈ graph →
        (VS.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {C : ENNReal}
    (hKT : let VS := firstCrossingFamilyVerticalSource axis F P k
      let graph := verticalSourceGraphCBucketFiber
        ((radius : Real) / 2) VS label
      IsKatzTao C (activeSubtypeFamily F.bodyFamily graph)) :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let VY := firstCrossingFamilyVerticalShading axis F P A k
    let graph := verticalSourceGraphCBucketFiber
      ((radius : Real) / 2) VS label
    let Dvertical := firstCrossingVerticalGraphSourceDatum axis F P A k
    let S8 := eighthNormalizedWZL3Source VS
    let Y8 := eighthNormalizedShading VS.family VY
    graph ⊆ S8.source ∧
      (∀ i, i ∈ graph →
        (S8.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) ∧
      IsFrostmanOn
        (eighthNormalizedActiveKatzTaoFrostmanConstant
          C Dvertical graph)
        S8.family.bodyFamily graph unitBallBody ∧
      (activeRestrictedShading S8 Y8 graph Set.univ
          MeasurableSet.univ).averageMultiplicity =
        (firstCrossingFamilyGraphBucketShading
          axis label F P A k).averageMultiplicity := by
  dsimp only at hB2 hKT ⊢
  let VS := firstCrossingFamilyVerticalSource axis F P k
  let VY := firstCrossingFamilyVerticalShading axis F P A k
  let graph := verticalSourceGraphCBucketFiber
    ((radius : Real) / 2) VS label
  let Dvertical := firstCrossingVerticalGraphSourceDatum axis F P A k
  let S8 := eighthNormalizedWZL3Source VS
  let Y8 := eighthNormalizedShading VS.family VY
  have hgraphSource : graph ⊆ S8.source := by
    intro i hi
    change i ∈ VS.source
    exact (mem_verticalSourceGraphCBucketFiber_iff
      ((radius : Real) / 2) VS label i).1 hi |>.1
  have hcontained : ∀ i, i ∈ graph →
      (S8.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
    simpa only [S8] using
      eighthNormalizedWZL3Source_active_carrier_subset_unitBall
        VS hradiusHalf graph hB2
  have hKTVertical : IsKatzTao C
      (activeSubtypeFamily VS.family.bodyFamily graph) := by
    have hforward :=
      isKatzTao_coordinateToVertical_activeSubtypeFamily
        axis F graph hKT
    have hfamily :
        VS.family.bodyFamily =
          (coordinateToVerticalFamily axis F).bodyFamily := by
      funext i
      rfl
    rw [hfamily]
    exact hforward
  have hFrostman : IsFrostmanOn
      (eighthNormalizedActiveKatzTaoFrostmanConstant
        C Dvertical graph)
      S8.family.bodyFamily graph unitBallBody := by
    have hraw := eighthNormalizedActive_isFrostmanOn_of_isKatzTao
      Dvertical graph hgraphNonempty hradius hradiusHalf hB2 hKTVertical
    have hfamily :
        (eighthNormalizedDatum Dvertical).family.bodyFamily =
          S8.family.bodyFamily := by
      funext i
      rfl
    rw [← hfamily]
    exact hraw
  have haverage :
      (activeRestrictedShading S8 Y8 graph Set.univ
        MeasurableSet.univ).averageMultiplicity =
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k).averageMultiplicity := by
    have hraw :=
      eighthNormalized_activeRestricted_univ_averageMultiplicity
        VS VY graph
    simpa only [S8, Y8, VS, VY, graph,
      firstCrossingFamilyGraphBucketShading] using hraw
  exact ⟨hgraphSource, hcontained, hFrostman, haverage⟩

#print axioms firstCrossingVerticalGraphSourceDatum
#print axioms firstCrossingGraph_fullCoefficientEighth_inputs

end
end Family8Family7FirstCrossingFullCoefficientEighthInputsV13
