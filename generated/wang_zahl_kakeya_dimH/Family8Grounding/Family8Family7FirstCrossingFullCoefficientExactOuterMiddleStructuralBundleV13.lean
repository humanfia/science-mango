import Family8Grounding.Family8Family7FirstCrossingFullCoefficientEighthDensityV12
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Family8Grounding.Family8Family7FirstCrossingFullCoefficientEighthInputsV13
import Family8Grounding.Family8Family7FirstCrossingFullCoefficientExactOuterGraphCertificateV1
import Family8Grounding.Family8Family7FirstCrossingFullCoefficientTripleV3

/-!
# Exact-outer same-object middle structural bundle, V13

This clean successor uses the explicit-family Inputs V13 and the literal
graph-nonempty Density V12 while keeping the exact same assembly, parent,
graph, and structural conclusions.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFullCoefficientExactOuterMiddleStructuralBundleV13

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8EighthNormalizedActiveKatzTaoFrostmanV4
open Family8EighthNormalizedWZL3SourceV3
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientEighthDensityV12
open Family8Family7FirstCrossingFullCoefficientEighthInputsV13
open Family8Family7FirstCrossingFullCoefficientExactOuterGraphCertificateV1
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7FirstCrossingFullCoefficientTripleV3
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FullCoefficientActualMassProxyAverageV10
open Family8KatzTaoFrostmanPropertiesV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- All geometry and exact identities on the single graph selected by an
exact-outer Family7 certificate. -/
structure FirstCrossingExactOuterMiddleStructuralBundle
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) {r : Real} (A : Assembly P Y r)
    (k : Fin T.coarseCard) (axis : Fin 3) (label : Int)
    (CF d graphLoss sourceLoss sourceAverage : ENNReal) where
  certificate : FirstCrossingFullCoefficientGraphCertificate
    F T P Y A k axis label CF d graphLoss
  source_retention : sourceAverage ≤
    sourceLoss * (actualRefinementShading A).averageMultiplicity
  exact_outer :
    A.frozenCoarse = P.inducedShading A.refinement.shading
  triple : sourceAverage ≤
    ((sourceLoss * 4 * graphLoss) *
        (firstCrossingFamilyGraphBucketShading
          axis label F P A k).averageMultiplicity) *
      A.frozenCoarse.averageMultiplicity
  graph_source :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS label
    let S8 := eighthNormalizedWZL3Source VS
    graph ⊆ S8.source
  unit_support :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS label
    let S8 := eighthNormalizedWZL3Source VS
    ∀ i, i ∈ graph →
      (S8.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1
  source_frostman :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS label
    let Dvertical := firstCrossingVerticalGraphSourceDatum axis F P A k
    let S8 := eighthNormalizedWZL3Source VS
    IsFrostmanOn
      (eighthNormalizedActiveKatzTaoFrostmanConstant
        (fullCoefficientGraphKatzTaoConstant axis label F T P k CF)
        Dvertical graph)
      S8.family.bodyFamily graph unitBallBody
  average_identity :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let VY := firstCrossingFamilyVerticalShading axis F P A k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS label
    let S8 := eighthNormalizedWZL3Source VS
    let Y8 := eighthNormalizedShading VS.family VY
    (activeRestrictedShading S8 Y8 graph Set.univ
      MeasurableSet.univ).averageMultiplicity =
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k).averageMultiplicity
  density_transport :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let VY := firstCrossingFamilyVerticalShading axis F P A k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS label
    let S8 := eighthNormalizedWZL3Source VS
    let Y8 := eighthNormalizedShading VS.family VY
    (selectedCoarseShading
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k) graph).shadingDensity / 128 ≤
      (activeRestrictedShading S8 Y8 graph Set.univ
        MeasurableSet.univ).shadingDensity
  density_lower :
    let VS := firstCrossingFamilyVerticalSource axis F P k
    let VY := firstCrossingFamilyVerticalShading axis F P A k
    let graph := verticalSourceGraphCBucketFiber
      ((tau : Real) / 2) VS label
    let S8 := eighthNormalizedWZL3Source VS
    let Y8 := eighthNormalizedShading VS.family VY
    d / graphLoss / 128 ≤
      (activeRestrictedShading S8 Y8 graph Set.univ
        MeasurableSet.univ).shadingDensity

/-- Construct the structural bundle directly from the exact-outer graph
certificate. -/
theorem of_exactOuterGraphCertificate
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) {r : Real} (A : Assembly P Y r)
    (k : Fin T.coarseCard) (axis : Fin 3) (label : Int)
    (CF d graphLoss sourceLoss sourceAverage : ENNReal)
    (Q : FirstCrossingFullCoefficientGraphCertificate
      F T P Y A k axis label CF d graphLoss)
    (hsource : sourceAverage ≤
      sourceLoss * (actualRefinementShading A).averageMultiplicity)
    (hexact :
      A.frozenCoarse = P.inducedShading A.refinement.shading)
    (htau : 0 < tau)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹) :
    FirstCrossingExactOuterMiddleStructuralBundle
      F T P Y A k axis label CF d graphLoss sourceLoss sourceAverage := by
  obtain ⟨hgraphSource, hunitSupport, hsourceFrostman,
      haverageIdentity⟩ :=
    firstCrossingGraph_fullCoefficientEighth_inputs
      axis label F P A k htau htauHalf Q.graph_nonempty
        Q.vertical_b2 Q.graph_katz_tao
  have hdensityTransport :=
    firstCrossingGraphBucket_density_div_128_le_eighthNormalized
      axis label F P A k Q.graph_nonempty htau htauHalf
  refine
    { certificate := Q
      source_retention := hsource
      exact_outer := hexact
      triple :=
        sourceAverage_le_fullCoefficientMiddle_mul_frozenCoarse
          F T P Y A k axis label CF d graphLoss sourceLoss
            sourceAverage Q hsource
      graph_source := hgraphSource
      unit_support := hunitSupport
      source_frostman := hsourceFrostman
      average_identity := haverageIdentity
      density_transport := hdensityTransport
      density_lower := ?_ }
  dsimp only
  let VS := firstCrossingFamilyVerticalSource axis F P k
  let VY := firstCrossingFamilyVerticalShading axis F P A k
  let graph := verticalSourceGraphCBucketFiber
    ((tau : Real) / 2) VS label
  let S8 := eighthNormalizedWZL3Source VS
  let Y8 := eighthNormalizedShading VS.family VY
  calc
    d / graphLoss / 128 ≤
        (selectedCoarseShading
          (firstCrossingFamilyGraphBucketShading
            axis label F P A k) graph).shadingDensity / 128 :=
      ENNReal.div_le_div_right Q.graph_density 128
    _ ≤ (activeRestrictedShading S8 Y8 graph Set.univ
          MeasurableSet.univ).shadingDensity := by
      simpa only [VS, VY, graph, S8, Y8] using hdensityTransport

#print axioms FirstCrossingExactOuterMiddleStructuralBundle
#print axioms of_exactOuterGraphCertificate

end
end Family8Family7FirstCrossingFullCoefficientExactOuterMiddleStructuralBundleV13
