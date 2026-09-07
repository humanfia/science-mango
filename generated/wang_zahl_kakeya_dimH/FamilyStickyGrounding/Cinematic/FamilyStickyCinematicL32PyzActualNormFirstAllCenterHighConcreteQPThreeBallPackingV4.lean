import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPThreeBallPackingV4

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPAggregationV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open Family4GlobalExtremalUpstream

noncomputable section

universe u

/-!
# Actual three-ball packing of the concrete Q/P high RHS

The rich-pair count and the number of high centers are now discharged by the
actual indexed `3B` overlap theorem.  The only quantitative factor left for a
paper packing argument is the transparent product of the bin loss, local and
third packing factors, sampled-lens bound, and wide area cap.
-/

/-- The rich ordered-pair cardinal appearing literally in one concrete RHS. -/
def nativeHighConcreteRichPairCard
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : Nat :=
  (richSeparatedCenterPairs
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).family
    (canonicalTenRadiusSeparated
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)) (G.ballRadius c))
    (fun _ _ => True)).card

/-- All local factors in the explicit concrete Q/P RHS except the rich-pair
cardinality.  The actual Q and P are the named witnesses from V4. -/
noncomputable def nativeHighConcreteResidualFactor
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) : ENNReal :=
  let H := D.chosenHighPayloadAt c
  let ballRadius := G.ballRadius c
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
        ballRadius h
  let P := positiveCenterHighPayload_baseConcreteP
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
        ballRadius h
  let referenceScale :=
    actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale P
  let comparisonLambda :=
    actualY1PaperFineCNormalizedAutomaticComparisonLambda
      (radius := radius) globalDelta D.globalScale (4 * ballRadius)
  let centerGap :=
    (401 / 100 : Real) * (ballRadius + 6 * D.globalScale)
  let curvatureRatio := twoCenterAutomaticCurvatureRatio
    (4 * ballRadius) centerGap referenceScale
  let codeBound : ENNReal := projectedCoefficientPackingCap ballRadius
    (2 * (ballRadius + 6 * D.globalScale))
  let localPacking := finiteOccupiedCodeLocalPacking
    comparisonLambda curvatureRatio
  let thirdPacking := finiteOccupiedCodeThirdPacking codeBound
    comparisonLambda curvatureRatio curvatureRatio
  let cap := actualGPrimeThreeShiftCGridWeightedE2WideCap
    (radius : Real) ballRadius globalDelta D.globalScale
  actualAllCenterPostNormBinLoss radius D.globalScale D.physical.ambient.card *
    (72 *
      (localPacking * thirdPacking *
        ENNReal.ofReal
          (sampledLensBound
            (selectedSubfamilyAutomaticDepthFromCurveBudget
              (actualThreeShiftCGridRestrictedGlobalTubeFamily
                P.gridSelection P.selected
                  (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                    (P := P))).card)
            (twoSidedZeroColorLoad 1 1 Q.sampled.omega)) * cap))

/-- Exact factorization of the V4 RHS into the transparent residual and its
literal rich-pair cardinality. -/
theorem concreteSampledLensRHS_eq_residual_mul_richPairCard
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    positiveCenterHighPayload_baseConcreteSampledLensRHS
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c) h =
      nativeHighConcreteResidualFactor D G c h *
        (nativeHighConcreteRichPairCard D G c : ENNReal) := by
  unfold positiveCenterHighPayload_baseConcreteSampledLensRHS
  unfold nativeHighConcreteResidualFactor nativeHighConcreteRichPairCard
  dsimp only
  ac_rfl

/-- Rich-pair squaring and the local ambient-card bound leave one copy of
the actual local `3B` cardinality for global overlap summation. -/
theorem concreteSampledLensRHS_le_residual_mul_ambient_mul_normCard
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    positiveCenterHighPayload_baseConcreteSampledLensRHS
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c) h <=
      (nativeHighConcreteResidualFactor D G c h *
          (D.ambient.card : ENNReal)) *
        (nativeHighNormFamilyCard D c : ENNReal) := by
  rw [concreteSampledLensRHS_eq_residual_mul_richPairCard]
  have hrich : nativeHighConcreteRichPairCard D G c <=
      nativeHighNormFamilyCard D c * nativeHighNormFamilyCard D c := by
    exact concreteRichPair_card_le_nativeHighNormFamilyCard_sq D G c
  have hrichCast : (nativeHighConcreteRichPairCard D G c : ENNReal) <=
      ((nativeHighNormFamilyCard D c * nativeHighNormFamilyCard D c : Nat) :
        ENNReal) := by
    exact_mod_cast hrich
  have hlocal : nativeHighNormFamilyCard D c <= D.ambient.card :=
    nativeHighNormFamilyCard_le_ambient_card D c
  have hsquare :
      nativeHighNormFamilyCard D c * nativeHighNormFamilyCard D c <=
        D.ambient.card * nativeHighNormFamilyCard D c :=
    Nat.mul_le_mul_right (nativeHighNormFamilyCard D c) hlocal
  have hsquareCast :
      ((nativeHighNormFamilyCard D c * nativeHighNormFamilyCard D c : Nat) :
          ENNReal) <=
        ((D.ambient.card * nativeHighNormFamilyCard D c : Nat) : ENNReal) := by
    exact_mod_cast hsquare
  calc
    nativeHighConcreteResidualFactor D G c h *
        (nativeHighConcreteRichPairCard D G c : ENNReal) <=
      nativeHighConcreteResidualFactor D G c h *
        ((nativeHighNormFamilyCard D c * nativeHighNormFamilyCard D c : Nat) :
          ENNReal) := mul_le_mul_right hrichCast _
    _ <= nativeHighConcreteResidualFactor D G c h *
        ((D.ambient.card * nativeHighNormFamilyCard D c : Nat) : ENNReal) :=
      mul_le_mul_right hsquareCast _
    _ = (nativeHighConcreteResidualFactor D G c h *
          (D.ambient.card : ENNReal)) *
        (nativeHighNormFamilyCard D c : ENNReal) := by
      rw [Nat.cast_mul]
      ac_rfl

/-- Once the single residual factor has a uniform upper bound, actual `3B`
overlap closes the entire cross-center sum. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_residualBound_mul_threeBallBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G)
    (hpair : Set.Pairwise (D.ambient : Set iota) fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j))
    (residualBound : ENNReal)
    (hresidual : forall (c : D.HighCenter)
      (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)),
      nativeHighConcreteResidualFactor D G c h <= residualBound) :
    D.sourceMass / 2 <=
      (residualBound * (D.ambient.card : ENNReal)) *
        ((19 ^ 3 * D.ambient.card : Nat) : ENNReal) := by
  obtain ⟨hlocal, hsum⟩ := hout
  apply hsum.trans
  calc
    (∑ c : D.HighCenter,
      positiveCenterHighPayload_baseConcreteSampledLensRHS
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)
              (hlocal c)) <=
      ∑ c : D.HighCenter,
        (residualBound * (D.ambient.card : ENNReal)) *
          (nativeHighNormFamilyCard D c : ENNReal) := by
      apply Finset.sum_le_sum
      intro c _hc
      apply (concreteSampledLensRHS_le_residual_mul_ambient_mul_normCard
        D G c (hlocal c)).trans
      exact mul_le_mul_left (mul_le_mul_left (hresidual c (hlocal c)) _) _
    _ = (residualBound * (D.ambient.card : ENNReal)) *
        (∑ c : D.HighCenter,
          (nativeHighNormFamilyCard D c : ENNReal)) := by
      rw [Finset.mul_sum]
    _ <= (residualBound * (D.ambient.card : ENNReal)) *
        ((19 ^ 3 * D.ambient.card : Nat) : ENNReal) :=
      mul_le_mul_right (sum_nativeHighNormFamilyCard_cast_le D hpair) _

/-- Physical-mass form: a pointwise residual bound by one common coefficient
times the actual projected shading mass gives the desired common-mass global
upper estimate. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_threeBallCoefficient_mul_physicalMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G)
    (hpair : Set.Pairwise (D.ambient : Set iota) fun i j =>
      EssentiallyDistinct (D.S.family.tubes i) (D.S.family.tubes j))
    (commonCoefficient : ENNReal)
    (hresidual : forall (c : D.HighCenter)
      (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)),
      nativeHighConcreteResidualFactor D G c h <=
        commonCoefficient * nativeHighPhysicalMass D) :
    D.sourceMass / 2 <=
      (((commonCoefficient * (D.ambient.card : ENNReal)) *
          ((19 ^ 3 * D.ambient.card : Nat) : ENNReal)) *
        nativeHighPhysicalMass D) := by
  calc
    D.sourceMass / 2 <=
        ((commonCoefficient * nativeHighPhysicalMass D) *
          (D.ambient.card : ENNReal)) *
            ((19 ^ 3 * D.ambient.card : Nat) : ENNReal) :=
      NativeHighConcreteQPOutcome.sourceMass_half_le_residualBound_mul_threeBallBudget
        hout hpair (commonCoefficient * nativeHighPhysicalMass D) hresidual
    _ = (((commonCoefficient * (D.ambient.card : ENNReal)) *
          ((19 ^ 3 * D.ambient.card : Nat) : ENNReal)) *
        nativeHighPhysicalMass D) := by
      ac_rfl

#print axioms nativeHighConcreteResidualFactor
#print axioms concreteSampledLensRHS_eq_residual_mul_richPairCard
#print axioms concreteSampledLensRHS_le_residual_mul_ambient_mul_normCard
#print axioms
  NativeHighConcreteQPOutcome.sourceMass_half_le_residualBound_mul_threeBallBudget
#print axioms
  NativeHighConcreteQPOutcome.sourceMass_half_le_threeBallCoefficient_mul_physicalMass

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPThreeBallPackingV4
