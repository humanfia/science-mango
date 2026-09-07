import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPThreeBallPackingV4
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedLoadBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPSampledLensEnvelopeV4

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedLoadBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# Cardinal envelope for the concrete high sampled-lens factor

Both colourings in the actual high endpoint take values in `Fin 1`.
Consequently every curve is selected, and the two-sided load is exactly
twice the cardinality of the concrete norm family.  The restricted final
tube family has no larger cardinality.  This removes the random sample and
the chosen Q/P witnesses from the sampled-lens numerical factor.
-/

/-- At one colour, every element of the finite domain is selected. -/
theorem zeroColorSample_one_card
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (omega : alpha -> Fin 1) :
    (zeroColorSample 1 omega).card = Fintype.card alpha := by
  have hall : zeroColorSample 1 omega = (Finset.univ : Finset alpha) := by
    ext a
    simp only [zeroColorSample, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (Subsingleton.elim (omega a) (0 : Fin 1))
  rw [hall, Finset.card_univ]

/-- At one colour, the two-sided load is exactly twice the common domain
cardinality. -/
theorem twoSidedZeroColorLoad_one_one_eq_twice_card
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (omega : (alpha -> Fin 1) × (alpha -> Fin 1)) :
    twoSidedZeroColorLoad 1 1 omega =
      2 * (Fintype.card alpha : Real) := by
  unfold twoSidedZeroColorLoad
  rw [zeroColorSample_one_card, zeroColorSample_one_card]
  ring

/-- Monotonicity of the automatic logarithmic depth in its natural curve
budget. -/
theorem selectedSubfamilyAutomaticDepthFromCurveBudget_mono
    {m n : Nat} (hmn : m <= n) :
    selectedSubfamilyAutomaticDepthFromCurveBudget m <=
      selectedSubfamilyAutomaticDepthFromCurveBudget n := by
  unfold selectedSubfamilyAutomaticDepthFromCurveBudget
  norm_cast
  exact Nat.add_le_add_right (Nat.log_mono_right (b := 2) hmn) 1

/-- A curve family of cardinality at most twice the common one-colour
domain has a sampled-lens factor bounded by the deterministic cardinal
envelope. -/
theorem sampledLensBound_oneColor_le_twiceCardEnvelope
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (curveBudget : Nat)
    (omega : (alpha -> Fin 1) × (alpha -> Fin 1))
    (hcurve : curveBudget <= 2 * Fintype.card alpha) :
    sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget curveBudget)
        (twoSidedZeroColorLoad 1 1 omega) <=
      sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget
          (2 * Fintype.card alpha))
        (2 * (Fintype.card alpha : Real)) := by
  have hdepth :=
    selectedSubfamilyAutomaticDepthFromCurveBudget_mono hcurve
  have hloadNonneg := twoSidedZeroColorLoad_nonneg 1 1 omega
  calc
    sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget curveBudget)
        (twoSidedZeroColorLoad 1 1 omega) <=
      sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget
          (2 * Fintype.card alpha))
        (twoSidedZeroColorLoad 1 1 omega) :=
      sampledLensBound_mono_depth hdepth hloadNonneg
    _ = sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget
          (2 * Fintype.card alpha))
        (2 * (Fintype.card alpha : Real)) := by
      rw [twoSidedZeroColorLoad_one_one_eq_twice_card]

/-- The actual final restricted tube family whose cardinality drives the
concrete automatic sampled-lens depth. -/
noncomputable def nativeHighConcreteCurveBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) : Nat :=
  let P := positiveCenterHighPayload_baseConcreteP
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent D.normExponent D.logCount
        (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c) h
  (actualThreeShiftCGridRestrictedGlobalTubeFamily
    P.gridSelection P.selected
      (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P))).card

/-- The concrete curve budget is at most twice the concrete norm-family
cardinality, with no source-pair multiplicity. -/
theorem nativeHighConcreteCurveBudget_le_twice_normFamilyCard
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    nativeHighConcreteCurveBudget D G c h <=
      2 * nativeHighNormFamilyCard D c := by
  let H := D.chosenHighPayloadAt c
  let N := positiveCenterHighPayloadGlobalNormData H
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent D.normExponent D.logCount
        H (G.mesh c) (G.ballRadius c) h
  let P := positiveCenterHighPayload_baseConcreteP
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent D.normExponent D.logCount
        H (G.mesh c) (G.ballRadius c) h
  let shift :=
    actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)
  have hcard :=
    actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_card_le_sample_cards
      N _ (fun _ _ => True) Q.sampled.pair.left Q.sampled.pair.right
        (G.ballRadius c) Q.sampled.omega P.gridSelection P.selected shift
  have hsamples :
      (zeroColorSample 1 Q.sampled.omega.1).card +
          (zeroColorSample 1 Q.sampled.omega.2).card =
        2 * N.family.card := by
    dsimp only [N]
    rw [zeroColorSample_one_card, zeroColorSample_one_card,
      Fintype.card_coe]
    omega
  have hmain :
      (actualThreeShiftCGridRestrictedGlobalTubeFamily
        P.gridSelection P.selected shift).card <= 2 * N.family.card :=
    hcard.trans_eq hsamples
  simpa only [nativeHighConcreteCurveBudget, H, N, P, shift,
    positiveCenterHighPayloadGlobalNormData_family,
    nativeHighNormFamilyCard] using hmain

/-- Deterministic sampled-lens envelope depending only on the actual norm
family cardinality. -/
noncomputable def nativeHighSampledLensCardinalEnvelope
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) : ENNReal :=
  ENNReal.ofReal
    (sampledLensBound
      (selectedSubfamilyAutomaticDepthFromCurveBudget
        (2 * nativeHighNormFamilyCard D c))
      (2 * (nativeHighNormFamilyCard D c : Real)))

/-- The literal sampled-lens factor in the concrete Q/P RHS is bounded by
the cardinal envelope, automatically and without a scalar callback. -/
theorem nativeHighConcreteSampledLensFactor_le_cardinalEnvelope
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    let Q := positiveCenterHighPayload_baseConcreteQ
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c) h
    ENNReal.ofReal
        (sampledLensBound
          (selectedSubfamilyAutomaticDepthFromCurveBudget
            (nativeHighConcreteCurveBudget D G c h))
          (twoSidedZeroColorLoad 1 1 Q.sampled.omega)) <=
      nativeHighSampledLensCardinalEnvelope D c := by
  dsimp only
  apply ENNReal.ofReal_le_ofReal
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  have hcardN :
      Fintype.card N.family = nativeHighNormFamilyCard D c := by
    rw [Fintype.card_coe]
    simp only [N, positiveCenterHighPayloadGlobalNormData_family,
      nativeHighNormFamilyCard]
  have hcurve :
      nativeHighConcreteCurveBudget D G c h <=
        2 * Fintype.card N.family := by
    rw [hcardN]
    exact nativeHighConcreteCurveBudget_le_twice_normFamilyCard D G c h
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent D.normExponent D.logCount
        (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c) h
  have hsample :=
    sampledLensBound_oneColor_le_twiceCardEnvelope
      (alpha := N.family)
      (nativeHighConcreteCurveBudget D G c h) Q.sampled.omega hcurve
  rw [hcardN] at hsample
  simpa only [Q] using hsample

#print axioms zeroColorSample_one_card
#print axioms twoSidedZeroColorLoad_one_one_eq_twice_card
#print axioms selectedSubfamilyAutomaticDepthFromCurveBudget_mono
#print axioms sampledLensBound_oneColor_le_twiceCardEnvelope
#print axioms nativeHighConcreteCurveBudget_le_twice_normFamilyCard
#print axioms nativeHighConcreteSampledLensFactor_le_cardinalEnvelope

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPSampledLensEnvelopeV4
