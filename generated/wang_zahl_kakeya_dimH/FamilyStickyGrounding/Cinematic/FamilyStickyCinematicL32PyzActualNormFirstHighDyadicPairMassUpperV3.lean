import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstHighCanonicalSharingCapV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitGlobalMassV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeWeightedPairMassDyadicUpperV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstHighDyadicPairMassUpperV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Prop41ActualGPrimeCanonicalSharingCapV3
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairIncidenceV2
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeWeightedPairMassDyadicUpperV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitGlobalMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstHighCanonicalSharingCapV2

noncomputable section

universe u

/-!
# Actual native-high dyadic pair-mass upper

The spatial fine labels of the actual E2 datum come from active-pattern
representatives inside the literal dyadic E2 cell.  Thus the generic dyadic
pair-mass upper applies with no extra hypothesis.  Combining it with the
global grid/shift synchronization and canonical sharing cap leaves the
explicit local loss `648 * cap^2 * degreeUpper^2`, multiplying the genuine
high-base mass.
-/

/-- The actual native-high weighted endpoint-pair mass is at most the square
of its E2 dyadic degree upper times the literal first-hit label mass. -/
theorem nativeHighWeightedFineSeparatedPairMass_le_degreeUpper_sq_mul_labelMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    let H := D.chosenHighPayloadAt c
    let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
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
    actualGPrimeWeightedFineSeparatedPairMass N R (fun _ _ => True)
        (actualGPrimeSurvivorSeparationRadius (G.ballRadius c))
          (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel) <=
      (((pyzE2DegreeUpper H.payload.finalLabel *
          pyzE2DegreeUpper H.payload.finalLabel : Nat) : ENNReal) *
        nativeHighPreMaxFirstHitLabelMass D G c) := by
  dsimp only
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
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
  let Y1 := actualCenteredHalfPaperFineY1 E_t hEt D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 (36 * D.globalScale) D.tangencyExponent globalDelta
  let source := actualCenteredHalfPaperFineE2 E_t hEt D.S.family D.physical
    H.payload.finalLabel D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf
      D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
        D.tangencyExponent globalDelta
  let patternAt := D.physical.activeAtPoint
  let fineLabels : Finset
      (ActualCenteredHalfPaperFineE2SpatialLabel E_t hEt D.S.family
        D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2 D.outerA
          D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
            (36 * D.globalScale) D.tangencyExponent globalDelta) :=
    Finset.univ
  let pointAt := spatialActivePatternRepresentative D.physical.ambient
    patternAt source (G.mesh c)
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta D.globalScale
  have hspatialLabels : R.fineLabels = fineLabels := by rfl
  have hpointAt : R.pointAt = pointAt := by rfl
  have hshading : R.shading = Y1 := by rfl
  obtain ⟨_hlabel, _hq, _hmass, _hEtPos, _hEtSubset, _hbin, _hE2Pos,
      _hE2Measurable, _hE2Subset, hactivePayload⟩ := H.payload.certificate
  have hactiveSource : forall q, q ∈ source ->
      (Y1.activeAtPoint q).Nonempty := by
    intro q hqSource
    have hqPositive : q ∈ positiveCenterE2 (D.highBase c)
        (D.highBase_measurable c) D.S.family D.physical D.f D.f1 D.f2
          D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
            D.tangencyExponent H.payload.tangencyLabel
              H.payload.finalLabel := by
      simpa only [source, Y1, actualCenteredHalfPaperFineE2,
        actualCenteredHalfPaperFineY1, positiveCenterE2, positiveCenterY1,
        positiveCenterTangencyCell, E_t, hEt, globalDelta] using hqSource
    obtain ⟨i, hi⟩ := hactivePayload q hqPositive
    refine ⟨i, ?_⟩
    simpa only [Y1, actualCenteredHalfPaperFineY1, positiveCenterY1,
      positiveCenterTangencyCell, E_t, hEt, globalDelta] using hi
  have hcell : forall r, r ∈ R.fineLabels ->
      R.pointAt r ∈ projectedPositiveMultiplicityDyadicCell
        R.shading H.payload.finalLabel := by
    intro r _hr
    rw [hpointAt, hshading]
    exact (spatialActivePatternRepresentative_spec D.physical.ambient
      patternAt source (G.mesh c) r).1
  have hactiveR : forall r, r ∈ R.fineLabels ->
      (R.shading.activeAtPoint (R.pointAt r)).Nonempty := by
    intro r hr
    rw [hpointAt, hshading]
    exact hactiveSource (pointAt r) (hcell r hr)
  have hRactual : R = actualCenteredHalfY1FineCoarseRectangleData E_t hEt
      D.S.family D.physical fineLabels pointAt D.f D.f1 D.f2 D.outerA
        D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
          (36 * D.globalScale) D.tangencyExponent globalDelta fineT
            globalDelta D.globalScale := by rfl
  have hsubsetR : forall r, r ∈ R.fineLabels ->
      R.shading.activeAtPoint (R.pointAt r) ⊆ N.family := by
    intro r hr
    rw [positiveCenterHighPayloadGlobalNormData_family, hRactual]
    exact actualCenteredHalfY1_activeAtFine_subset_globalNormIndexFamily
      E_t hEt D.S.family D.physical fineLabels pointAt D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
      (36 * D.globalScale) D.tangencyExponent globalDelta fineT
      globalDelta D.globalScale r (by simpa only [hspatialLabels] using hr)
  have hupper :=
    actualGPrimeWeightedFineSeparatedPairMass_le_degreeUpper_sq_mul_weightSum
      N R H.payload.finalLabel
        (actualGPrimeSurvivorSeparationRadius (G.ballRadius c))
          (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
            hcell hactiveR hsubsetR
  simpa only [nativeHighPreMaxFirstHitLabelMass, H, E_t, hEt,
    globalDelta, R] using hupper

/-- Callback-free local endpoint: after synchronization and actual-pair
sharing, the native high pre-max mass is charged to its high-base mass with
the explicit factor `648 * canonicalCap^2 * degreeUpper^2`. -/
theorem nativeHighPreMaxFirstHitCenterPairMass_le_canonicalCap_sq_mul_degreeUpper_sq_mul_highBase
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    let H := D.chosenHighPayloadAt c
    let N := positiveCenterHighPayloadGlobalNormData H
    nativeHighPreMaxFirstHitCenterPairMass D G c <=
      648 *
        (((automaticCanonicalCenterSharingNatCap N (G.ballRadius c) *
          automaticCanonicalCenterSharingNatCap N (G.ballRadius c) : Nat) :
            ENNReal) *
          (((pyzE2DegreeUpper H.payload.finalLabel *
            pyzE2DegreeUpper H.payload.finalLabel : Nat) : ENNReal) *
              volume (D.highBase c))) := by
  dsimp only
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
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
  have hsharing :=
    nativeHighPreMaxFirstHitCenterPairMass_le_canonicalCap_sq_mul_pairMass
      D G c h
  have hdyadic :=
    nativeHighWeightedFineSeparatedPairMass_le_degreeUpper_sq_mul_labelMass
      D G c
  have hlabel := nativeHighPreMaxFirstHitLabelMass_le_highBase D G c h
  calc
    nativeHighPreMaxFirstHitCenterPairMass D G c <=
        648 *
          (((automaticCanonicalCenterSharingNatCap N (G.ballRadius c) *
            automaticCanonicalCenterSharingNatCap N (G.ballRadius c) : Nat) :
              ENNReal) *
            actualGPrimeWeightedFineSeparatedPairMass N R (fun _ _ => True)
              (actualGPrimeSurvivorSeparationRadius (G.ballRadius c))
                (actualGPrimeE2FirstHitLabelWeight
                  R H.payload.finalLabel)) := by
      simpa only [H, E_t, hEt, globalDelta, N, R] using hsharing
    _ <= 648 *
          (((automaticCanonicalCenterSharingNatCap N (G.ballRadius c) *
            automaticCanonicalCenterSharingNatCap N (G.ballRadius c) : Nat) :
              ENNReal) *
            (((pyzE2DegreeUpper H.payload.finalLabel *
              pyzE2DegreeUpper H.payload.finalLabel : Nat) : ENNReal) *
                nativeHighPreMaxFirstHitLabelMass D G c)) := by
      gcongr
    _ <= 648 *
          (((automaticCanonicalCenterSharingNatCap N (G.ballRadius c) *
            automaticCanonicalCenterSharingNatCap N (G.ballRadius c) : Nat) :
              ENNReal) *
            (((pyzE2DegreeUpper H.payload.finalLabel *
              pyzE2DegreeUpper H.payload.finalLabel : Nat) : ENNReal) *
                volume (D.highBase c))) := by
      gcongr

#print axioms nativeHighWeightedFineSeparatedPairMass_le_degreeUpper_sq_mul_labelMass
#print axioms nativeHighPreMaxFirstHitCenterPairMass_le_canonicalCap_sq_mul_degreeUpper_sq_mul_highBase

end

end FamilyStickyCinematicL32PyzActualNormFirstHighDyadicPairMassUpperV3
