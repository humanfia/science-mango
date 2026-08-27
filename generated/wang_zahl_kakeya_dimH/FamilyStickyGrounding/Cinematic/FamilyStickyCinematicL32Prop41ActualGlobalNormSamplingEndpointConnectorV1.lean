import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Actual shared-global survivor endpoints feed the finite lens counter

This module instantiates the general retained-pair endpoint assembly on the
literal survivor subtype and on the two genuine sampled hit witnesses.  Thus
the sampling callback below is a consequence of the geometric endpoint
package, rather than a bare assumed lens inequality.
-/

/-- The literal finite fiber of surviving rectangles for one sampling
outcome. -/
noncomputable def actualSharedGlobalSurvivorFiber
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
    Finset (TwoSidedZeroColorSurvivor mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega) :=
  Finset.univ

/-- The actual tube chosen by the genuine left zero-colour hit of a survivor. -/
noncomputable def actualSharedGlobalSurvivorLeftTube
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
    TwoSidedZeroColorSurvivor mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega -> Tube radius :=
  fun R => D.fine.tubes
    (survivorLeftHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega R).1.1

/-- Right-hit counterpart of `actualSharedGlobalSurvivorLeftTube`. -/
noncomputable def actualSharedGlobalSurvivorRightTube
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
    TwoSidedZeroColorSurvivor mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega -> Tube radius :=
  fun R => D.fine.tubes
    (survivorRightHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega R).1.1

/-- A survivor carries the source rectangle to which its two sampled hits
belong. -/
def actualSharedGlobalSurvivorRectangle
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
    TwoSidedZeroColorSurvivor mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega ->
      C2GraphRectangle :=
  fun R => R.1.1

/-- The helper fiber has exactly the cardinality used on the left side of the
sampling certificate. -/
theorem actualSharedGlobalSurvivorFiber_card
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
    (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega).card =
      (twoSidedZeroColorSurvivors mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega).card := by
  simp only [actualSharedGlobalSurvivorFiber, Finset.card_univ,
    Fintype.card_coe]

/-- The retained family generated by the helper fiber and endpoint maps is
definitionally the literal actual survivor family used by sampling. -/
theorem actualSharedGlobalSurvivorRetainedTubeFamily_eq
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
    retainedPairTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega) =
      actualSharedGlobalSurvivorRetainedTubeFamily fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega := by
  rfl

/-- Monotonicity in the depth parameter, isolated because the survivor
assembly naturally returns its canonical depth while the sampling theorem
may use one uniform upper bound for every outcome. -/
theorem sampledLensBound_mono_depth
    {depth depth' curveCount : Real}
    (hdepth : depth <= depth') (hcurve : 0 <= curveCount) :
    sampledLensBound depth curveCount <=
      sampledLensBound depth' curveCount := by
  have hsqrt : 0 <= Real.sqrt curveCount := Real.sqrt_nonneg _
  have hproduct : 0 <= curveCount * Real.sqrt curveCount :=
    mul_nonneg hcurve hsqrt
  unfold sampledLensBound
  nlinarith [mul_nonneg (sub_nonneg.mpr hdepth) hproduct]

/-- To build a sampling callback it suffices to construct the geometric
certificate when the survivor finset is nonempty.  Empty outcomes are closed
numerically, without requesting a fictitious endpoint assembly. -/
theorem actualSharedGlobalSurvivorLensCertificate_of_nonempty_case
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
    (depth : Real) (hdepth : 0 <= depth)
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (hnonempty :
      (twoSidedZeroColorSurvivors mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega).Nonempty ->
      ActualSharedGlobalSurvivorLensCertificate fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu depth omega) :
    ActualSharedGlobalSurvivorLensCertificate fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu depth omega := by
  by_cases hsurvivor : (twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega).Nonempty
  · exact hnonempty hsurvivor
  · have hcard : (twoSidedZeroColorSurvivors mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hsurvivor)
    unfold ActualSharedGlobalSurvivorLensCertificate
    rw [hcard]
    unfold sampledLensBound
    norm_num
    positivity
/-- Endpoint assembly specialized to one literal shared-global sampling
outcome. -/
abbrev ActualSharedGlobalSurvivorEndpointAssembly
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
    (weight : Tube radius -> Real) (f f1 : Real -> Real)
    (center : C2GraphRectangle) (domain : Set Real)
    (A B delta t lambda1 comparisonLambda externalTolerance : Real) :=
  PerturbedRetainedPairEndpointAssembly
    (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    (actualSharedGlobalSurvivorRectangle fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega)
    weight f f1 center domain A B delta t lambda1 comparisonLambda
      externalTolerance

/-- The explicit selected-lens estimate in a survivor endpoint assembly is
exactly an ActualSharedGlobalSurvivorLensCertificate.  No raw lens-count
inequality is assumed.  A possibly larger depth may be supplied so one
uniform depth works for all sampling outcomes. -/
theorem actualSharedGlobalSurvivorLensCertificate_of_endpointAssembly
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
    (weight : Tube radius -> Real) (f f1 f2 : Real -> Real)
    (center : C2GraphRectangle) {domain : Set Real}
    {A B delta t lambda1 comparisonLambda externalTolerance : Real}
    (S : ActualSharedGlobalSurvivorEndpointAssembly fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega
      weight f f1 center domain A B delta t lambda1 comparisonLambda
        externalTolerance)
    (depth : Real)
    (hdepth :
      (canonicalDepth (FirstGenerationCurve
        (perturbedRetainedTubeFamily
          (actualSharedGlobalSurvivorFiber fine physical globalScale
            globalCenter D keep rectangles left right ballRadius mu nu omega)
          (actualSharedGlobalSurvivorLeftTube fine physical globalScale
            globalCenter D keep rectangles left right ballRadius mu nu omega)
          (actualSharedGlobalSurvivorRightTube fine physical globalScale
            globalCenter D keep rectangles left right ballRadius mu nu omega)
          weight S.epsilon)) : Real) <= depth)
    (hAB : A < B) (M : Real)
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda1 : 1 <= lambda1)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale :
      prop41TangencyScaleFactor (4 * lambda1) * delta < t / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hgraphBound : forall V,
      V ∈ perturbedRetainedTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        weight S.epsilon -> forall theta, theta ∈ Icc A B ->
          |actualTubeGraph V f theta| <= M)
    (henlarge : 2 * lambda1 * delta <= comparisonLambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda1) delta t <=
      Real.sqrt (comparisonLambda * delta / t))
    (hreference : forall V,
      V ∈ perturbedRetainedTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        weight S.epsilon ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB.le)
        (3 * t)) :
    ActualSharedGlobalSurvivorLensCertificate fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu depth omega := by
  let fiber := actualSharedGlobalSurvivorFiber fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let T := actualSharedGlobalSurvivorLeftTube fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let U := actualSharedGlobalSurvivorRightTube fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let source := actualSharedGlobalSurvivorRectangle fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let curves := perturbedRetainedTubeFamily fiber T U weight S.epsilon
  have hbound : (fiber.card : Real) <=
      sampledLensBound
        (canonicalDepth (FirstGenerationCurve curves) : Real)
        (curves.card : Real) := by
    simpa only [sampledLensBound, fiber, T, U, source, curves] using
      pairLocalActualSelectedLens_card_le_explicit_global_of_endpointAssembly
        fiber T U source weight f f1 f2 center S hAB M hdelta ht hlambda1
        hwidth hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower
        hf1Upper hf2 hf2Continuous hgraphBound henlarge hscale hreference
  have hdepthBound : sampledLensBound
      (canonicalDepth (FirstGenerationCurve curves) : Real)
      (curves.card : Real) <= sampledLensBound depth (curves.card : Real) :=
    sampledLensBound_mono_depth hdepth (by positivity)
  have hcurveCard : curves.card =
      (actualSharedGlobalSurvivorRetainedTubeFamily fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega).card := by
    calc
      curves.card = (retainedPairTubeFamily fiber T U).card := S.family_card_eq
      _ = (actualSharedGlobalSurvivorRetainedTubeFamily fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega).card := by
        exact congrArg Finset.card
          (actualSharedGlobalSurvivorRetainedTubeFamily_eq fine physical
            globalScale globalCenter D keep rectangles left right ballRadius
              mu nu omega)
  have hfiberCard : fiber.card =
      (twoSidedZeroColorSurvivors mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega).card := by
    exact actualSharedGlobalSurvivorFiber_card fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega
  unfold ActualSharedGlobalSurvivorLensCertificate
  rw [← hfiberCard, ← hcurveCard]
  exact hbound.trans hdepthBound
/-- A strengthened three-shift package on the literal survivor pairs produces
the sampling lens certificate without any assumed sampled-lens inequality.
The perturbation is chosen internally.  Consequently the graph and reference
bounds are stated uniformly over the allowed perturbation interval; all other
inputs are the explicit geometric hypotheses of the endpoint producer. -/
theorem actualSharedGlobalSurvivorLensCertificate_of_perturbationReady
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
    (weight : Tube radius -> Real) (f f1 f2 : Real -> Real)
    (center : C2GraphRectangle) {domain : Set Real}
    {A B delta t lambda0 lambda1 comparisonLambda externalTolerance depth : Real}
    (hsurvivor : (twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega).Nonempty)
    (hexternalTolerance : 0 < externalTolerance)
    (hAB : A < B) (hdelta : 0 < delta) (ht : 0 < t)
    (hlambda1 : 1 <= lambda1)
    (hwidth : (1 / 2 : Real) <= B - A)
    (P : forall i, i ∈
      actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega ->
      PerturbationReadyPairLocalActualLensRectangleData
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega i)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega i)
        f
        (actualSharedGlobalSurvivorRectangle fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega i)
        A B delta t lambda0 lambda1)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda1) * delta <
      t / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcommonC : forall V, V ∈ retainedPairTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega) -> forall W,
      W ∈ retainedPairTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega) ->
        tubeGraphC V = tubeGraphC W)
    (hweight : Set.InjOn weight
      (retainedPairTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega) :
        Set (Tube radius)))
    (hcritical : forall V,
      V ∈ retainedPairTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega) ->
      forall W,
      W ∈ retainedPairTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega) ->
      V ≠ W ->
        (criticalHeightDifferenceSet
          (fun X => actualTubeGraph X f)
          (fun X => actualTubeGraphFirst X f f1) A B V W).Finite)
    (henlarge : 2 * lambda1 * delta <= comparisonLambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda1) delta t <=
      Real.sqrt (comparisonLambda * delta / t))
    (hreference : forall epsilon, 0 < epsilon ->
      epsilon < externalTolerance -> forall V,
      V ∈ perturbedRetainedTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        weight epsilon ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB.le)
        (3 * t))
    (hpairwise : Set.Pairwise
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega : Set _)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center
        (actualSharedGlobalSurvivorRectangle fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega i)
        (actualSharedGlobalSurvivorRectangle fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega j)
        delta t comparisonLambda)))
    (hdepth :
      (canonicalDepth (FirstGenerationCurve
        (actualSharedGlobalSurvivorRetainedTubeFamily fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)) :
          Real) <= depth)
    (M : Real)
    (hgraphBound : forall epsilon, 0 < epsilon ->
      epsilon < externalTolerance -> forall V,
      V ∈ perturbedRetainedTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        weight epsilon -> forall theta, theta ∈ Icc A B ->
          |actualTubeGraph V f theta| <= M) :
    ActualSharedGlobalSurvivorLensCertificate fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu depth omega := by
  let fiber := actualSharedGlobalSurvivorFiber fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let T := actualSharedGlobalSurvivorLeftTube fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let U := actualSharedGlobalSurvivorRightTube fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let source := actualSharedGlobalSurvivorRectangle fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  have hfiber : fiber.Nonempty := by
    obtain ⟨R, hR⟩ := hsurvivor
    exact ⟨⟨R, hR⟩, Finset.mem_univ _⟩
  obtain ⟨S⟩ :=
    exists_perturbedRetainedPairEndpointAssembly_of_perturbationReady
      fiber hfiber T U source weight f f1 f2 center
      hexternalTolerance hAB hdelta ht hlambda1 hwidth P hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hcommonC hweight hcritical henlarge hscale hreference hpairwise
  have hdepthS :
      (canonicalDepth (FirstGenerationCurve
        (perturbedRetainedTubeFamily fiber T U weight S.epsilon)) : Real) <=
          depth := by
    have hcard :
        (perturbedRetainedTubeFamily fiber T U weight S.epsilon).card =
          (actualSharedGlobalSurvivorRetainedTubeFamily fine physical
            globalScale globalCenter D keep rectangles left right ballRadius
              mu nu omega).card := by
      calc
        (perturbedRetainedTubeFamily fiber T U weight S.epsilon).card =
            (retainedPairTubeFamily fiber T U).card := S.family_card_eq
        _ = (actualSharedGlobalSurvivorRetainedTubeFamily fine physical
            globalScale globalCenter D keep rectangles left right ballRadius
              mu nu omega).card := by
          exact congrArg Finset.card
            (actualSharedGlobalSurvivorRetainedTubeFamily_eq fine physical
              globalScale globalCenter D keep rectangles left right ballRadius
                mu nu omega)
    have hcanonical : canonicalDepth (FirstGenerationCurve
        (perturbedRetainedTubeFamily fiber T U weight S.epsilon)) =
        canonicalDepth (FirstGenerationCurve
          (actualSharedGlobalSurvivorRetainedTubeFamily fine physical
            globalScale globalCenter D keep rectangles left right ballRadius
              mu nu omega)) := by
      unfold canonicalDepth
      simp only [Fintype.card_coe, hcard]
    simpa only [hcanonical] using hdepth
  exact actualSharedGlobalSurvivorLensCertificate_of_endpointAssembly
    fine physical globalScale globalCenter D keep rectangles left right
    ballRadius mu nu omega weight f f1 f2 center S depth hdepthS hAB M
    hdelta ht hlambda1 hwidth hfDeriv hf1Deriv hsmallScale hparameter hft
    hf1Lower hf1Upper hf2 hf2Continuous
    (hgraphBound S.epsilon S.epsilon_pos S.epsilon_lt_external)
    henlarge hscale
    (hreference S.epsilon S.epsilon_pos S.epsilon_lt_external)

#print axioms actualSharedGlobalSurvivorFiber
#print axioms actualSharedGlobalSurvivorLeftTube
#print axioms actualSharedGlobalSurvivorRightTube
#print axioms actualSharedGlobalSurvivorRectangle
#print axioms actualSharedGlobalSurvivorFiber_card
#print axioms actualSharedGlobalSurvivorRetainedTubeFamily_eq
#print axioms sampledLensBound_mono_depth
#print axioms actualSharedGlobalSurvivorLensCertificate_of_nonempty_case
#print axioms ActualSharedGlobalSurvivorEndpointAssembly
#print axioms actualSharedGlobalSurvivorLensCertificate_of_endpointAssembly
#print axioms actualSharedGlobalSurvivorLensCertificate_of_perturbationReady
end

end FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
