import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingPaperShapeNoLensAssumptionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1

open Set
open scoped BigOperators
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Automatic finite-family graph and depth bounds

The horizontal trace translation used by the finite-general-position
argument adds exactly `epsilon * weight T` to the actual tube graph.  Thus a
finite family needs no pointwise graph-bound callback: the sum of explicit
coefficient envelopes, together with the finite sum of absolute weights,
gives one uniform bound for every sufficiently small perturbation.

The sampling depth is equally canonical.  Choosing the real coercion of the
`canonicalDepth` of the retained actual tube family makes the requested depth
comparison reflexive and its nonnegativity automatic.
-/

/-- A coefficient-only upper envelope for one actual tube graph on
`|theta| <= 1` and under `|f theta| <= 2`. -/
def actualTubeGraphCoefficientEnvelope {radius : NNReal}
    (T : Tube radius) : Real :=
  |skirtTubeGraphA T| + |skirtTubeGraphC T| +
    2 * (|skirtTubeGraphB T| + |skirtTubeGraphD T|)

theorem actualTubeGraphCoefficientEnvelope_nonneg
    {radius : NNReal} (T : Tube radius) :
    0 <= actualTubeGraphCoefficientEnvelope T := by
  unfold actualTubeGraphCoefficientEnvelope
  positivity

/-- The explicit coefficient envelope controls the unperturbed actual graph. -/
theorem abs_actualTubeGraph_le_coefficientEnvelope
    {radius : NNReal} (T : Tube radius) (f : Real -> Real) (theta : Real)
    (htheta : |theta| <= 1) (hf : |f theta| <= 2) :
    |actualTubeGraph T f theta| <= actualTubeGraphCoefficientEnvelope T := by
  have hcTheta : |skirtTubeGraphC T * theta| <= |skirtTubeGraphC T| := by
    calc
      |skirtTubeGraphC T * theta| =
          |skirtTubeGraphC T| * |theta| := abs_mul _ _
      _ <= |skirtTubeGraphC T| * 1 :=
        mul_le_mul_of_nonneg_left htheta (abs_nonneg _)
      _ = |skirtTubeGraphC T| := mul_one _
  have hdTheta : |skirtTubeGraphD T * theta| <= |skirtTubeGraphD T| := by
    calc
      |skirtTubeGraphD T * theta| =
          |skirtTubeGraphD T| * |theta| := abs_mul _ _
      _ <= |skirtTubeGraphD T| * 1 :=
        mul_le_mul_of_nonneg_left htheta (abs_nonneg _)
      _ = |skirtTubeGraphD T| := mul_one _
  have hinner :
      |skirtTubeGraphB T + skirtTubeGraphD T * theta| <=
        |skirtTubeGraphB T| + |skirtTubeGraphD T| := by
    exact (abs_add_le _ _).trans (add_le_add le_rfl hdTheta)
  have hproduct :
      |f theta * (skirtTubeGraphB T + skirtTubeGraphD T * theta)| <=
        2 * (|skirtTubeGraphB T| + |skirtTubeGraphD T|) := by
    rw [abs_mul]
    exact mul_le_mul hf hinner (abs_nonneg _) (by norm_num)
  unfold actualTubeGraph actualTubeGraphCoefficientEnvelope
  calc
    |skirtTubeGraphA T + skirtTubeGraphC T * theta +
        f theta * (skirtTubeGraphB T + skirtTubeGraphD T * theta)| <=
        |skirtTubeGraphA T + skirtTubeGraphC T * theta| +
          |f theta * (skirtTubeGraphB T +
            skirtTubeGraphD T * theta)| := abs_add_le _ _
    _ <= (|skirtTubeGraphA T| +
          |skirtTubeGraphC T * theta|) +
        |f theta * (skirtTubeGraphB T +
          skirtTubeGraphD T * theta)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ <= (|skirtTubeGraphA T| + |skirtTubeGraphC T|) +
        2 * (|skirtTubeGraphB T| + |skirtTubeGraphD T|) :=
      add_le_add (add_le_add le_rfl hcTheta) hproduct
    _ = |skirtTubeGraphA T| + |skirtTubeGraphC T| +
        2 * (|skirtTubeGraphB T| + |skirtTubeGraphD T|) := rfl

/-- Sum envelope for a finite family.  A sum is used instead of a maximum so
the empty family and all order bookkeeping remain completely canonical. -/
def finiteActualTubeFamilyGraphEnvelope {radius : NNReal}
    (curves : Finset (Tube radius)) : Real :=
  ∑ T ∈ curves, actualTubeGraphCoefficientEnvelope T

/-- Finite absolute-weight envelope.  This automatically incorporates the
`weight * epsilon` perturbation without a separately assumed weight bound. -/
def finiteActualTubeFamilyWeightEnvelope {radius : NNReal}
    (curves : Finset (Tube radius)) (weight : Tube radius -> Real) : Real :=
  ∑ T ∈ curves, |weight T|

theorem finiteActualTubeFamilyGraphEnvelope_nonneg
    {radius : NNReal} (curves : Finset (Tube radius)) :
    0 <= finiteActualTubeFamilyGraphEnvelope curves := by
  unfold finiteActualTubeFamilyGraphEnvelope
  exact Finset.sum_nonneg fun T _ => actualTubeGraphCoefficientEnvelope_nonneg T

theorem finiteActualTubeFamilyWeightEnvelope_nonneg
    {radius : NNReal} (curves : Finset (Tube radius))
    (weight : Tube radius -> Real) :
    0 <= finiteActualTubeFamilyWeightEnvelope curves weight := by
  unfold finiteActualTubeFamilyWeightEnvelope
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem coefficientEnvelope_le_finiteFamilyEnvelope
    {radius : NNReal} {curves : Finset (Tube radius)} {T : Tube radius}
    (hT : T ∈ curves) :
    actualTubeGraphCoefficientEnvelope T <=
      finiteActualTubeFamilyGraphEnvelope curves := by
  unfold finiteActualTubeFamilyGraphEnvelope
  exact Finset.single_le_sum
    (fun V _ => actualTubeGraphCoefficientEnvelope_nonneg V) hT

theorem abs_weight_le_finiteFamilyWeightEnvelope
    {radius : NNReal} {curves : Finset (Tube radius)}
    (weight : Tube radius -> Real) {T : Tube radius} (hT : T ∈ curves) :
    |weight T| <= finiteActualTubeFamilyWeightEnvelope curves weight := by
  unfold finiteActualTubeFamilyWeightEnvelope
  exact Finset.single_le_sum
    (fun V (_ : V ∈ curves) => abs_nonneg (weight V)) hT

/-- Fully explicit bound for every member of the independently translated
finite family and every `0 < epsilon < externalTolerance`. -/
def finiteActualTubeFamilyPerturbedGraphBound {radius : NNReal}
    (curves : Finset (Tube radius)) (weight : Tube radius -> Real)
    (externalTolerance : Real) : Real :=
  finiteActualTubeFamilyGraphEnvelope curves +
    externalTolerance * finiteActualTubeFamilyWeightEnvelope curves weight

theorem finiteActualTubeFamilyPerturbedGraphBound_nonneg
    {radius : NNReal} (curves : Finset (Tube radius))
    (weight : Tube radius -> Real) {externalTolerance : Real}
    (hexternalTolerance : 0 <= externalTolerance) :
    0 <= finiteActualTubeFamilyPerturbedGraphBound
      curves weight externalTolerance := by
  unfold finiteActualTubeFamilyPerturbedGraphBound
  exact add_nonneg (finiteActualTubeFamilyGraphEnvelope_nonneg curves)
    (mul_nonneg hexternalTolerance
      (finiteActualTubeFamilyWeightEnvelope_nonneg curves weight))

theorem individuallyTracePerturbedTubeFamily_graph_le_finite_bound
    {radius : NNReal} (curves : Finset (Tube radius))
    (weight : Tube radius -> Real) (f : Real -> Real)
    {externalTolerance epsilon : Real}
    (hexternalTolerance : 0 < externalTolerance)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < externalTolerance)
    {V : Tube radius}
    (hV : V ∈ individuallyTracePerturbedTubeFamily curves weight epsilon)
    (theta : Real) (htheta : |theta| <= 1) (hf : |f theta| <= 2) :
    |actualTubeGraph V f theta| <=
      finiteActualTubeFamilyPerturbedGraphBound
        curves weight externalTolerance := by
  simp only [individuallyTracePerturbedTubeFamily, Finset.mem_image] at hV
  obtain ⟨T, hT, rfl⟩ := hV
  have hgraph : |actualTubeGraph T f theta| <=
      finiteActualTubeFamilyGraphEnvelope curves :=
    (abs_actualTubeGraph_le_coefficientEnvelope T f theta htheta hf).trans
      (coefficientEnvelope_le_finiteFamilyEnvelope hT)
  have hweight : |weight T| <=
      finiteActualTubeFamilyWeightEnvelope curves weight :=
    abs_weight_le_finiteFamilyWeightEnvelope weight hT
  have hshift : |epsilon * weight T| <=
      externalTolerance * finiteActualTubeFamilyWeightEnvelope curves weight := by
    rw [abs_mul, abs_of_pos hepsilon]
    exact mul_le_mul hepsilon_lt.le hweight (abs_nonneg _)
      hexternalTolerance.le
  rw [actualTubeGraph_individuallyTracePerturbedTube]
  unfold finiteActualTubeFamilyPerturbedGraphBound
  exact (abs_add_le _ _).trans (add_le_add hgraph hshift)

/-- The bound specialized to the literal retained-pair perturbation family. -/
def retainedPairPerturbedGraphBound
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (weight : Tube radius -> Real) (externalTolerance : Real) : Real :=
  finiteActualTubeFamilyPerturbedGraphBound
    (retainedPairTubeFamily fiber T U) weight externalTolerance

theorem perturbedRetainedTubeFamily_graph_le_automatic_bound
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (weight : Tube radius -> Real) (f : Real -> Real)
    {externalTolerance epsilon : Real}
    (hexternalTolerance : 0 < externalTolerance)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < externalTolerance)
    {V : Tube radius}
    (hV : V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon)
    (theta : Real) (htheta : |theta| <= 1) (hf : |f theta| <= 2) :
    |actualTubeGraph V f theta| <=
      retainedPairPerturbedGraphBound
        fiber T U weight externalTolerance := by
  rw [perturbedRetainedTubeFamily_eq_individuallyTracePerturbedTubeFamily]
    at hV
  exact individuallyTracePerturbedTubeFamily_graph_le_finite_bound
    (retainedPairTubeFamily fiber T U) weight f hexternalTolerance
      hepsilon hepsilon_lt hV theta htheta hf

/-! ## Literal shared-global sampling specialization -/

/-- The computable graph bound for one actual shared-global survivor fiber. -/
def actualSharedGlobalSurvivorAutomaticGraphBound
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
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (weight : Tube radius -> Real) (externalTolerance : Real) : Real :=
  retainedPairPerturbedGraphBound
    (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    weight externalTolerance

/-- The exact `perturbed_graph_bound` field required by
`ActualSharedGlobalSurvivorGeometryPackage`, generated solely from finite
actual-tube coefficients, the finite weight family, `|theta| <= 1`, and
`|f theta| <= 2`. -/
theorem actualSharedGlobalSurvivor_perturbed_graph_bound_automatic
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
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (weight : Tube radius -> Real) (f : Real -> Real)
    (A B externalTolerance : Real)
    (hexternalTolerance : 0 < externalTolerance)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hfunction : forall theta, theta ∈ Icc A B -> |f theta| <= 2) :
    forall epsilon, 0 < epsilon -> epsilon < externalTolerance -> forall V,
      V ∈ perturbedRetainedTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        weight epsilon -> forall theta, theta ∈ Icc A B ->
        |actualTubeGraph V f theta| <=
          actualSharedGlobalSurvivorAutomaticGraphBound fine physical
            globalScale globalCenter D keep rectangles left right ballRadius
              mu nu omega weight externalTolerance := by
  intro epsilon hepsilon hepsilon_lt V hV theta htheta
  exact perturbedRetainedTubeFamily_graph_le_automatic_bound
    (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    weight f hexternalTolerance hepsilon hepsilon_lt hV theta
      (hparameter theta htheta) (hfunction theta htheta)

/-- Canonical choice of the real-valued sampling depth. -/
def actualSharedGlobalSurvivorAutomaticDepth
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
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu)) : Real :=
  canonicalDepth (FirstGenerationCurve
    (actualSharedGlobalSurvivorRetainedTubeFamily fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega))

theorem actualSharedGlobalSurvivorAutomaticDepth_nonneg
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
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu)) :
    0 <= actualSharedGlobalSurvivorAutomaticDepth fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega := by
  unfold actualSharedGlobalSurvivorAutomaticDepth
  positivity

/-- Choosing the automatic depth discharges the geometry package's
`depth_bound` field by reflexivity. -/
theorem actualSharedGlobalSurvivor_depth_bound_automatic
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
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu)) :
    (canonicalDepth (FirstGenerationCurve
      (actualSharedGlobalSurvivorRetainedTubeFamily fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)) :
        Real) <=
      actualSharedGlobalSurvivorAutomaticDepth fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega := by
  rfl

#print axioms abs_actualTubeGraph_le_coefficientEnvelope
#print axioms perturbedRetainedTubeFamily_graph_le_automatic_bound
#print axioms actualSharedGlobalSurvivor_perturbed_graph_bound_automatic
#print axioms actualSharedGlobalSurvivor_depth_bound_automatic

end

end FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
