import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPExactWeightedResidualSumV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWideSourceFirstHitGeometryV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitMassBudgetV4

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWideSourceFirstHitGeometryV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u v

/-!
# The actual selected first-hit mass across all high centres

The weighted `Q/P` route assigns to every fine label the volume of its
literal first-hit `Y₂` piece.  This module keeps that weight through the
concrete selected package and proves that the sum over every high centre is
bounded by the same norm-cell source mass.  No area cap, cardinal envelope,
or desired multiplicity conclusion is assumed.

This identity does not by itself cancel the remaining rich-pair
`ambient.card`: such a cancellation still needs a packing estimate that
keeps the selected first-hit weight paired with the rich-pair coefficient.
-/

/-- An injective finite family of labels has no more nonnegative weight than
the full target carrier. -/
theorem sum_comp_injective_le_sum_carrier
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [DecidableEq alpha] [DecidableEq beta]
    (carrier : Finset beta) (labelAt : alpha -> beta)
    (hinjective : Function.Injective labelAt)
    (hmem : forall a, labelAt a ∈ carrier)
    (weight : beta -> ENNReal) :
    (∑ a : alpha, weight (labelAt a)) <=
      ∑ b ∈ carrier, weight b := by
  classical
  calc
    (∑ a : alpha, weight (labelAt a)) =
        ∑ b ∈ (Finset.univ : Finset alpha).image labelAt, weight b := by
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      exact hinjective hab
    _ <= ∑ b ∈ carrier, weight b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hb
        exact hmem a
      · intro _b _hb _hnot
        exact bot_le

/-- The first-hit weight retained by one concrete `P.selected` is no larger
than the full first-hit label mass from which it was selected. -/
theorem finiteENNRealWeight_selectedFirstHit_le_fineLabels
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D keep left right ballRadius omega labelWeight f outerA outerB
        globalDelta tGlobal) :
    finiteENNRealWeight P.selected
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius
          omega labelWeight) <=
      ∑ r ∈ D.fineLabels, labelWeight r := by
  let labelAt := actualGPrimeLabelFirstLabel
    N D keep left right ballRadius omega
  let weightAt := actualGPrimeLabelFirstSurvivorWeightAt
    N D keep left right ballRadius omega labelWeight
  calc
    finiteENNRealWeight P.selected weightAt <=
        ∑ a : ActualGPrimeLabelFirstSurvivor
          N D keep left right ballRadius omega, weightAt a := by
      unfold finiteENNRealWeight
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ P.selected) (fun _ _ _ => bot_le)
    _ <= ∑ r ∈ D.fineLabels, labelWeight r := by
      apply sum_comp_injective_le_sum_carrier D.fineLabels labelAt
        P.label_injective
      · intro a
        exact actualGPrimeLabelFirstLabel_mem_fineLabels
          N D keep left right ballRadius omega a

/-- The literal selected first-hit mass in the actual `Q/P` package at one
native high centre. -/
noncomputable def nativeHighConcreteSelectedFirstHitMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) : ENNReal :=
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
        D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let N := positiveCenterHighPayloadGlobalNormData H
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  let P := positiveCenterHighPayload_baseConcreteP
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  finiteENNRealWeight P.selected
    (actualGPrimeLabelFirstSurvivorWeightAt N R (fun _ _ => True)
      Q.sampled.pair.left Q.sampled.pair.right (G.ballRadius c)
        Q.sampled.omega
          (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel))

/-- At one high centre the concrete selected first-hit mass is bounded by
the literal high-base mass. -/
theorem nativeHighConcreteSelectedFirstHitMass_le_highBase
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    nativeHighConcreteSelectedFirstHitMass D G c h <=
      volume (D.highBase c) := by
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
        D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let N := positiveCenterHighPayloadGlobalNormData H
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  let P := positiveCenterHighPayload_baseConcreteP
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  have hselected := finiteENNRealWeight_selectedFirstHit_le_fineLabels
    D.S.family N R (fun _ _ => True) Q.sampled.pair.left
      Q.sampled.pair.right (G.ballRadius c) Q.sampled.omega
        (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
          D.f D.outerA D.outerB globalDelta D.globalScale P
  have hmass := Q.firstHit_mass_eq
  obtain ⟨_hlabel, _hq, _hmass, _hEtPos, hEtSubset, _htangencyBin,
      _hE2Pos, _hE2Measurable, hE2Subset, _hactive⟩ :=
    H.payload.certificate
  calc
    nativeHighConcreteSelectedFirstHitMass D G c h <=
        ∑ r ∈ R.fineLabels,
          actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r := by
      change finiteENNRealWeight P.selected
        (actualGPrimeLabelFirstSurvivorWeightAt N R (fun _ _ => True)
          Q.sampled.pair.left Q.sampled.pair.right (G.ballRadius c)
            Q.sampled.omega
              (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)) <=
        ∑ r ∈ R.fineLabels,
          actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r
      exact hselected
    _ = volume (projectedPositiveMultiplicityDyadicCell R.shading
        H.payload.finalLabel) := hmass
    _ <= volume (D.highBase c) := by
      apply measure_mono
      simpa only [R, actualCenteredHalfPaperFineE2SpatialIncidenceData,
        actualCenteredHalfProjectedE2SpatialIncidenceData,
        y1FineCoarseRectangleData, actualCenteredHalfPaperFineY1,
        actualCenteredHalfPaperFineE2, positiveCenterE2,
        positiveCenterY1, positiveCenterTangencyCell, E_t, hEt,
        globalDelta] using hE2Subset.trans hEtSubset

/-- Across all high centres, every selected first-hit piece is charged to
the same norm-cell source mass. -/
theorem NativeHighConcreteQPOutcome.sum_selectedFirstHitMass_le_sourceMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) :
    let hlocal := nativeHighConcreteQPLocalAt hout
    (∑ c : D.HighCenter,
      nativeHighConcreteSelectedFirstHitMass D G c (hlocal c)) <=
        D.sourceMass := by
  dsimp only
  let hlocal := nativeHighConcreteQPLocalAt hout
  calc
    (∑ c : D.HighCenter,
      nativeHighConcreteSelectedFirstHitMass D G c (hlocal c)) <=
        ∑ c : D.HighCenter, volume (D.highBase c) := by
      exact Finset.sum_le_sum fun c _hc =>
        nativeHighConcreteSelectedFirstHitMass_le_highBase
          D G c (hlocal c)
    _ = ∑ c ∈ D.high, volume (D.cell c.1) := by
      simpa only [NativeBranchCore.highBase, NativeBranchCore.positiveBase,
        Finset.univ_eq_attach] using
          Finset.sum_attach D.high (fun c => volume (D.cell c.1))
    _ <= ∑ c : D.PositiveCenter, volume (D.cell c.1) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ D.high) (fun _ _ _ => bot_le)
    _ = ∑ center ∈ actualAllCenterPositiveCenters volume D.centers D.cell,
        volume (D.cell center) := by
      simpa only [Finset.univ_eq_attach] using
        Finset.sum_attach
          (actualAllCenterPositiveCenters volume D.centers D.cell)
          (fun center => volume (D.cell center))
    _ <= ∑ center ∈ D.centers, volume (D.cell center) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => bot_le)
    _ = D.sourceMass := D.hsourceMass.symm

#print axioms sum_comp_injective_le_sum_carrier
#print axioms finiteENNRealWeight_selectedFirstHit_le_fineLabels
#print axioms nativeHighConcreteSelectedFirstHitMass
#print axioms nativeHighConcreteSelectedFirstHitMass_le_highBase
#print axioms NativeHighConcreteQPOutcome.sum_selectedFirstHitMass_le_sourceMass

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitMassBudgetV4
