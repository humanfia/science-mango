import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPSampledLensEnvelopeV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPResidualEnvelopeV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPThreeBallPackingV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPSampledLensEnvelopeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u

/-!
# Deterministic residual envelope after actual three-ball packing

The random sampled-lens term is replaced by a deterministic function of the
ambient cardinality.  What remains pointwise is the transparent geometric
factor

`binLoss * 72 * localPacking * thirdPacking * wideCap`.

No power estimate for this factor is asserted here.  In particular the two
ambient-card factors created by the actual three-ball packing remain visible
in the final theorem and are not presented as a small loss.
-/

/-- The literal sampled-lens factor occurring inside the concrete residual. -/
noncomputable def nativeHighConcreteSampledLensFactor
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) : ENNReal :=
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent D.normExponent D.logCount
        (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c) h
  ENNReal.ofReal
    (sampledLensBound
      (selectedSubfamilyAutomaticDepthFromCurveBudget
        (nativeHighConcreteCurveBudget D G c h))
      (twoSidedZeroColorLoad 1 1 Q.sampled.omega))

/-- All remaining pointwise geometric factors after removing both the rich
pair cardinality and the sampled-lens term. -/
noncomputable def nativeHighConcreteGeometricFactor
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) : ENNReal :=
  let H := D.chosenHighPayloadAt c
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let P := positiveCenterHighPayload_baseConcreteP
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent D.normExponent D.logCount
        H (G.mesh c) (G.ballRadius c) h
  let referenceScale :=
    actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale P
  let comparisonLambda :=
    actualY1PaperFineCNormalizedAutomaticComparisonLambda
      (radius := radius) globalDelta D.globalScale (4 * G.ballRadius c)
  let centerGap :=
    (401 / 100 : Real) * (G.ballRadius c + 6 * D.globalScale)
  let curvatureRatio := twoCenterAutomaticCurvatureRatio
    (4 * G.ballRadius c) centerGap referenceScale
  let codeBound : ENNReal := projectedCoefficientPackingCap (G.ballRadius c)
    (2 * (G.ballRadius c + 6 * D.globalScale))
  let localPacking :=
    finiteOccupiedCodeLocalPacking comparisonLambda curvatureRatio
  let thirdPacking := finiteOccupiedCodeThirdPacking codeBound
    comparisonLambda curvatureRatio curvatureRatio
  let cap := actualGPrimeThreeShiftCGridWeightedE2WideCap
    (radius : Real) (G.ballRadius c) globalDelta D.globalScale
  actualAllCenterPostNormBinLoss radius D.globalScale
      D.physical.ambient.card *
    (72 * (localPacking * thirdPacking * cap))

/-- Exact refactoring of the concrete residual into the remaining geometry
and the literal sampled-lens factor. -/
theorem nativeHighConcreteResidualFactor_eq_geometric_mul_sampledLens
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    nativeHighConcreteResidualFactor D G c h =
      nativeHighConcreteGeometricFactor D G c h *
        nativeHighConcreteSampledLensFactor D G c h := by
  unfold nativeHighConcreteResidualFactor
    nativeHighConcreteGeometricFactor nativeHighConcreteSampledLensFactor
    nativeHighConcreteCurveBudget
  dsimp only
  ac_rfl

/-- One common deterministic sampled-lens envelope, now depending only on
the actual ambient cardinality. -/
noncomputable def nativeHighGlobalSampledLensCardinalEnvelope
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) : ENNReal :=
  ENNReal.ofReal
    (sampledLensBound
      (selectedSubfamilyAutomaticDepthFromCurveBudget
        (2 * D.ambient.card))
      (2 * (D.ambient.card : Real)))

/-- The local cardinal envelope is no larger than the common ambient one. -/
theorem nativeHighSampledLensCardinalEnvelope_le_global
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    nativeHighSampledLensCardinalEnvelope D c <=
      nativeHighGlobalSampledLensCardinalEnvelope D := by
  apply ENNReal.ofReal_le_ofReal
  have hcard := nativeHighNormFamilyCard_le_ambient_card D c
  have htwoNat :
      2 * nativeHighNormFamilyCard D c <= 2 * D.ambient.card :=
    Nat.mul_le_mul_left 2 hcard
  have hdepth :=
    selectedSubfamilyAutomaticDepthFromCurveBudget_mono htwoNat
  have hcountReal :
      2 * (nativeHighNormFamilyCard D c : Real) <=
        2 * (D.ambient.card : Real) := by
    exact_mod_cast htwoNat
  calc
    sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget
          (2 * nativeHighNormFamilyCard D c))
        (2 * (nativeHighNormFamilyCard D c : Real)) <=
      sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget
          (2 * D.ambient.card))
        (2 * (nativeHighNormFamilyCard D c : Real)) :=
      sampledLensBound_mono_depth hdepth (by positivity)
    _ <= sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget
          (2 * D.ambient.card))
        (2 * (D.ambient.card : Real)) :=
      sampledLensBound_mono_curveCount
        (selectedSubfamilyAutomaticDepthFromCurveBudget_nonneg _)
        (by positivity) hcountReal

/-- The concrete sampled-lens factor is bounded by the common ambient
envelope, with all Q/P sample dependence removed. -/
theorem nativeHighConcreteSampledLensFactor_le_globalEnvelope
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    nativeHighConcreteSampledLensFactor D G c h <=
      nativeHighGlobalSampledLensCardinalEnvelope D := by
  calc
    nativeHighConcreteSampledLensFactor D G c h <=
        nativeHighSampledLensCardinalEnvelope D c := by
      exact nativeHighConcreteSampledLensFactor_le_cardinalEnvelope D G c h
    _ <= nativeHighGlobalSampledLensCardinalEnvelope D :=
      nativeHighSampledLensCardinalEnvelope_le_global D c

/-- Pointwise no-callback residual envelope. -/
theorem nativeHighConcreteResidualFactor_le_geometric_mul_globalEnvelope
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    nativeHighConcreteResidualFactor D G c h <=
      nativeHighConcreteGeometricFactor D G c h *
        nativeHighGlobalSampledLensCardinalEnvelope D := by
  rw [nativeHighConcreteResidualFactor_eq_geometric_mul_sampledLens]
  exact mul_le_mul_right
    (nativeHighConcreteSampledLensFactor_le_globalEnvelope D G c h) _

/-- Cross-center endpoint with only the transparent geometric factor left
as a uniform quantitative premise.  The ambient-card square is explicit. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_geometricBound_mul_globalEnvelope
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G)
    (hpair : Set.Pairwise (D.ambient : Set iota) fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j))
    (geometricBound : ENNReal)
    (hgeometry : forall (c : D.HighCenter)
      (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)),
      nativeHighConcreteGeometricFactor D G c h <= geometricBound) :
    D.sourceMass / 2 <=
      ((geometricBound * nativeHighGlobalSampledLensCardinalEnvelope D) *
        (D.ambient.card : ENNReal)) *
          ((19 ^ 3 * D.ambient.card : Nat) : ENNReal) := by
  apply
    NativeHighConcreteQPOutcome.sourceMass_half_le_residualBound_mul_threeBallBudget
      hout hpair
        (geometricBound * nativeHighGlobalSampledLensCardinalEnvelope D)
  intro c h
  calc
    nativeHighConcreteResidualFactor D G c h <=
        nativeHighConcreteGeometricFactor D G c h *
          nativeHighGlobalSampledLensCardinalEnvelope D :=
      nativeHighConcreteResidualFactor_le_geometric_mul_globalEnvelope
        D G c h
    _ <= geometricBound * nativeHighGlobalSampledLensCardinalEnvelope D :=
      mul_le_mul_left (hgeometry c h) _

#print axioms nativeHighConcreteSampledLensFactor
#print axioms nativeHighConcreteGeometricFactor
#print axioms nativeHighConcreteResidualFactor_eq_geometric_mul_sampledLens
#print axioms nativeHighSampledLensCardinalEnvelope_le_global
#print axioms nativeHighConcreteSampledLensFactor_le_globalEnvelope
#print axioms nativeHighConcreteResidualFactor_le_geometric_mul_globalEnvelope
#print axioms
  NativeHighConcreteQPOutcome.sourceMass_half_le_geometricBound_mul_globalEnvelope

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPResidualEnvelopeV3
