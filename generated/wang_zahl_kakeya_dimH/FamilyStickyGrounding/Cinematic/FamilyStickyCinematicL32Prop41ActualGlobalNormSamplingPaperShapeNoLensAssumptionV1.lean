import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingPaperShapeNoLensAssumptionV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Paper-shaped actual shared-global sampling without a lens-count assumption

For each nonempty sampling outcome the package below records exactly the
geometry consumed by the finite-general-position endpoint producer and the
explicit selected-lens counter.  Empty outcomes are discharged by the
totalizer in the preceding connector module.
-/

/-- Honest outcome-local geometry replacing the former bare sampled-lens
inequality.  The chosen perturbation weight, all scale parameters, and the
comparison reference are data; the remaining fields are the precise
perturbation-ready and counting hypotheses used downstream. -/
structure ActualSharedGlobalSurvivorGeometryPackage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (f f1 f2 : Real -> Real) (A B depth : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu)) where
  weight : Tube radius -> Real
  center : C2GraphRectangle
  domain : Set Real
  delta : Real
  t : Real
  lambda0 : Real
  lambda1 : Real
  comparisonLambda : Real
  externalTolerance : Real
  graphBound : Real
  externalTolerance_pos : 0 < externalTolerance
  interval_strict : A < B
  delta_pos : 0 < delta
  t_pos : 0 < t
  lambda1_ge_one : 1 <= lambda1
  interval_width : (1 / 2 : Real) <= B - A
  perturbationReady : forall i, i ∈
      actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega ->
    PerturbationReadyPairLocalActualLensRectangleData
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega i)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega i)
      f
      (actualSharedGlobalSurvivorRectangle fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega i)
      A B delta t lambda0 lambda1
  small_scale : prop41TangencyScaleFactor (4 * lambda1) * delta < t / 1200
  parameter_bound : forall z, z ∈ Icc A B -> |z| <= 1
  graph_function_bound : forall z, z ∈ Icc A B -> |f z| <= 2
  first_derivative_lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|
  first_derivative_upper : forall z, z ∈ Icc A B -> |f1 z| <= 2
  second_derivative_bound : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100
  second_derivative_continuous : ContinuousOn f2 (Icc A B)
  common_c : forall V, V ∈ retainedPairTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega) -> forall W,
    W ∈ retainedPairTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega) ->
      tubeGraphC V = tubeGraphC W
  weight_injective : Set.InjOn weight
    (retainedPairTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega) : Set (Tube radius))
  critical_finite : forall V,
    V ∈ retainedPairTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega) -> forall W,
    W ∈ retainedPairTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega) -> V ≠ W ->
      (criticalHeightDifferenceSet
        (fun X => actualTubeGraph X f)
        (fun X => actualTubeGraphFirst X f f1) A B V W).Finite
  comparison_enlarges :
    2 * lambda1 * delta <= comparisonLambda * delta
  localization_scale : 4 * prop41ActualPairLocalizationRadius
      (4 * lambda1) delta t <= Real.sqrt (comparisonLambda * delta / t)
  reference : forall epsilon, 0 < epsilon ->
    epsilon < externalTolerance -> forall V,
    V ∈ perturbedRetainedTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      weight epsilon ->
    InPointwiseC2BallOn domain center
      (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B
        interval_strict.le) (3 * t)
  source_pairwise : Set.Pairwise
    (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega : Set _)
    (fun i j => Not (compactC2SymmetricGraphLambdaComparableOn
      domain center
      (actualSharedGlobalSurvivorRectangle fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega i)
      (actualSharedGlobalSurvivorRectangle fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega j)
      delta t comparisonLambda))
  depth_bound :
    (canonicalDepth (FirstGenerationCurve
      (actualSharedGlobalSurvivorRetainedTubeFamily fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)) :
        Real) <= depth
  perturbed_graph_bound : forall epsilon, 0 < epsilon ->
    epsilon < externalTolerance -> forall V,
    V ∈ perturbedRetainedTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      weight epsilon -> forall theta, theta ∈ Icc A B ->
        |actualTubeGraph V f theta| <= graphBound

/-- Paper-shaped shared-global sampling bound with no sampled-lens inequality
among its hypotheses.  A geometric package is requested only for nonempty
survivor outcomes; the empty case is automatic. -/
theorem actualCenteredHalfY1_rectangleCard_le_sharedGlobal_sampledLensPaperShape_mu_nu_of_geometry
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (hleftCard : forall R, R ∈ rectangles ->
      mu <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius left).card)
    (hrightCard : forall R, R ∈ rectangles ->
      nu <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius right).card)
    (depth : Real) (hdepth : 0 <= depth)
    (hgeometry : forall omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu),
      (twoSidedZeroColorSurvivors mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega).Nonempty ->
      ActualSharedGlobalSurvivorGeometryPackage fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu
          f f1 f2 outerA outerB depth hf hf1 omega) :
    let ambient :=
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    let load := 7 * ((ambient.card : Real) / (mu : Real) +
      (ambient.card : Real) / (nu : Real))
    ((rectangles.card : Nat) : Real) <=
      8 * (316 + 48 * depth) * load * Real.sqrt load := by
  have hcertificate : forall omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu),
      ActualSharedGlobalSurvivorLensCertificate fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu depth
          omega := by
    intro omega
    apply actualSharedGlobalSurvivorLensCertificate_of_nonempty_case
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu depth hdepth omega
    intro hsurvivor
    let G := hgeometry omega hsurvivor
    exact actualSharedGlobalSurvivorLensCertificate_of_perturbationReady
      fine physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega G.weight f f1 f2 G.center hsurvivor
      G.externalTolerance_pos G.interval_strict G.delta_pos G.t_pos
      G.lambda1_ge_one G.interval_width G.perturbationReady hf hf1
      G.small_scale G.parameter_bound G.graph_function_bound
      G.first_derivative_lower G.first_derivative_upper
      G.second_derivative_bound G.second_derivative_continuous G.common_c
      G.weight_injective G.critical_finite G.comparison_enlarges
      G.localization_scale G.reference G.source_pairwise G.depth_bound
      G.graphBound G.perturbed_graph_bound
  exact
    actualCenteredHalfY1_rectangleCard_le_sharedGlobal_sampledLensPaperShape_mu_nu
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT D hD keep rectangles left right ballRadius mu nu
      hleftCard hrightCard depth hdepth hcertificate

#print axioms ActualSharedGlobalSurvivorGeometryPackage
#print axioms actualCenteredHalfY1_rectangleCard_le_sharedGlobal_sampledLensPaperShape_mu_nu_of_geometry
end

end FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingPaperShapeNoLensAssumptionV1
