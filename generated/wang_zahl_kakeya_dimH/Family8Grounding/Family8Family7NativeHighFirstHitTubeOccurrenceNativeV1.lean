import Family8Grounding.Family8Family7NativeHighFirstHitTubeOccurrenceWeightV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7NativeHighFirstHitTubeOccurrenceWeightV1
open Family8Family7NativeHighWeightedCriticalBallV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u

/-!
# Native first-hit tube-occurrence weight

This successor specializes the exact fine-label Fubini weight to one literal
native high centre.  The nonemptiness of every retained fibre is derived from
the already-produced E2 degree lower bound and `NativeHighGeometry.hroom`.
No fibre, mass, critical-ball, or desired-conclusion callback is added.
-/

/-- The literal spatial E2 incidence datum at one native high centre. -/
noncomputable def nativeHighFirstHitIncidenceData
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :=
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent

/-- The canonical norm datum used by the same local producer. -/
noncomputable def nativeHighFirstHitNormData
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :=
  positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)

/-- Honest first-hit occurrence weight on the original tube index. -/
noncomputable def nativeHighFirstHitTubeOccurrenceWeight
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (i : iota) : ENNReal :=
  actualGPrimeE2FirstHitTubeOccurrenceWeight
    (nativeHighFirstHitNormData D c) (nativeHighFirstHitIncidenceData D G c)
      (D.chosenHighPayloadAt c).payload.finalLabel i

/-- The same native occurrence weight, installed in the weighted canonical
critical-ball selector. -/
noncomputable def nativeHighFirstHitWeightedNormData
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : WeightedCanonicalNormBallData iota :=
  actualGPrimeE2FirstHitWeightedNormData
    (nativeHighFirstHitNormData D c) (nativeHighFirstHitIncidenceData D G c)
      (D.chosenHighPayloadAt c).payload.finalLabel

/-- The E2 degree-room inequality makes every literal retained fine fibre
nonempty.  This removes the final raw fibre hypothesis from occurrence
Fubini at a native high centre. -/
theorem nativeHighFirstHitRetainedFiber_nonempty
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    let N := nativeHighFirstHitNormData D c
    let R := nativeHighFirstHitIncidenceData D G c
    ∀ r, r ∈ R.fineLabels →
      (actualGPrimeRetainedFineActiveFiber
        N R (fun _ _ => True) r).Nonempty := by
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
  change ∀ r, r ∈ R.fineLabels →
    (actualGPrimeRetainedFineActiveFiber
      N R (fun _ _ => True) r).Nonempty
  have hspatialLabels : R.fineLabels = fineLabels := by rfl
  have hpointAt : R.pointAt = pointAt := by rfl
  have hshading : R.shading = Y1 := by rfl
  obtain ⟨_hlabel, _hq, _hmass, _hEtPos, _hEtSubset, _hbin, _hE2Pos,
      _hE2Measurable, _hE2Subset, hactivePayload⟩ := H.payload.certificate
  have hactiveSource : ∀ q, q ∈ source →
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
  have hcell : ∀ r, r ∈ R.fineLabels →
      R.pointAt r ∈ projectedPositiveMultiplicityDyadicCell
        R.shading H.payload.finalLabel := by
    intro r _hr
    rw [hpointAt, hshading]
    exact (spatialActivePatternRepresentative_spec D.physical.ambient
      patternAt source (G.mesh c) r).1
  have hactiveR : ∀ r, r ∈ R.fineLabels →
      (R.shading.activeAtPoint (R.pointAt r)).Nonempty := by
    intro r hr
    rw [hpointAt, hshading]
    exact hactiveSource (pointAt r) (hcell r hr)
  have hRactual : R = actualCenteredHalfY1FineCoarseRectangleData E_t hEt
      D.S.family D.physical fineLabels pointAt D.f D.f1 D.f2 D.outerA
        D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
          (36 * D.globalScale) D.tangencyExponent globalDelta fineT
            globalDelta D.globalScale := by rfl
  have hsubsetR : ∀ r, r ∈ R.fineLabels →
      R.shading.activeAtPoint (R.pointAt r) ⊆ N.family := by
    intro r hr
    rw [positiveCenterHighPayloadGlobalNormData_family, hRactual]
    exact actualCenteredHalfY1_activeAtFine_subset_globalNormIndexFamily
      E_t hEt D.S.family D.physical fineLabels pointAt D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
      (36 * D.globalScale) D.tangencyExponent globalDelta fineT
      globalDelta D.globalScale r (by simpa only [hspatialLabels] using hr)
  intro r hr
  have hdegree : pyzE2DegreeLower H.payload.finalLabel ≤
      (actualGPrimeRetainedFineActiveFiber
        N R (fun _ _ => True) r).card :=
    pyzE2DegreeLower_le_actualGPrimeRetainedFineActiveFiber_true
      N R H.payload.finalLabel r hr (hcell r hr) (hactiveR r hr)
        (hsubsetR r hr)
  have hdegreePos : 0 < pyzE2DegreeLower H.payload.finalLabel := by
    have hroom := G.hroom c
    change automaticCanonicalNearCap N (G.ballRadius c) <
      pyzE2DegreeLower H.payload.finalLabel at hroom
    omega
  exact Finset.card_pos.mp (hdegreePos.trans_le hdegree)

/-- The native occurrence weight retains the exact projected first-hit E2
mass.  The only proposition argument is the actual local conclusion already
produced by the high branch, used solely to name its literal `Q`. -/
theorem sum_nativeHighFirstHitTubeOccurrenceWeight_eq_E2Mass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    let H := D.chosenHighPayloadAt c
    let N := nativeHighFirstHitNormData D c
    let R := nativeHighFirstHitIncidenceData D G c
    (∑ i ∈ N.family, nativeHighFirstHitTubeOccurrenceWeight D G c i) =
      volume (projectedPositiveMultiplicityDyadicCell
        R.shading H.payload.finalLabel) := by
  let H := D.chosenHighPayloadAt c
  let N := nativeHighFirstHitNormData D c
  let R := nativeHighFirstHitIncidenceData D G c
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  change (∑ i ∈ N.family,
      actualGPrimeE2FirstHitTubeOccurrenceWeight
        N R H.payload.finalLabel i) =
    volume (projectedPositiveMultiplicityDyadicCell
      R.shading H.payload.finalLabel)
  exact sum_actualGPrimeE2FirstHitTubeOccurrenceWeight_eq_E2Mass
    N R H.payload.finalLabel (G.ballRadius c) Q
      (nativeHighFirstHitRetainedFiber_nonempty D G c)

#print axioms nativeHighFirstHitIncidenceData
#print axioms nativeHighFirstHitNormData
#print axioms nativeHighFirstHitTubeOccurrenceWeight
#print axioms nativeHighFirstHitWeightedNormData
#print axioms nativeHighFirstHitRetainedFiber_nonempty
#print axioms sum_nativeHighFirstHitTubeOccurrenceWeight_eq_E2Mass

end

end Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1
