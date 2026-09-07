import Family8Grounding.Family8Family7ActivePatternOccurrenceWeightV1
import Family8Grounding.Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1
import Family8Grounding.Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighActivePatternOccurrenceProducerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7ActivePatternOccurrenceWeightV1
open Family8Family7ActivePatternOccurrenceWeightV1.ActivePatternOccurrenceData
open Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1
open Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u

/-!
# Native pattern-first occurrence producer

The native high E2 cell is partitioned by its literal physical active
pattern.  The local occurrence fibre is the actual centered-half Y1 fibre.
Thus every occurrence is physically active throughout its exact event, while
the equal-share weights retain the whole E2 mass.
-/

def nativeHighActivePatternSource
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : Set (Real × Real) :=
  projectedPositiveMultiplicityDyadicCell
    (nativeHighFirstHitIncidenceData D G c).shading
    (D.chosenHighPayloadAt c).payload.finalLabel

/-- The genuine native producer.  All fields are extracted from the existing
positive-centre payload and the literal centered-half Y1 construction. -/
theorem nativeHighActivePatternOccurrenceData
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    ActivePatternOccurrenceData (nativeHighFirstHitNormData D c) D.physical
      (nativeHighFirstHitIncidenceData D G c).shading
      (nativeHighActivePatternSource D G c) := by
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
  change ActivePatternOccurrenceData N D.physical R.shading
    (projectedPositiveMultiplicityDyadicCell
      R.shading H.payload.finalLabel)
  have hshading : R.shading = Y1 := by rfl
  obtain ⟨_hlabel, _hq, _hmass, _hEtPos, _hEtSubset, _hbin, _hE2Pos,
      _hE2Measurable, _hE2Subset, hactivePayload⟩ := H.payload.certificate
  refine
    { source_measurable := ?_
      local_active_nonempty := ?_
      local_active_subset_physical := ?_
      local_active_subset_family := ?_ }
  · exact measurableSet_projectedPositiveMultiplicityDyadicCell
      R.shading H.payload.finalLabel
  · intro q hq
    rw [hshading] at hq ⊢
    have hqPositive : q ∈ positiveCenterE2 (D.highBase c)
        (D.highBase_measurable c) D.S.family D.physical D.f D.f1 D.f2
          D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
            D.tangencyExponent H.payload.tangencyLabel
              H.payload.finalLabel := by
      simpa only [Y1, actualCenteredHalfPaperFineY1, positiveCenterE2,
        positiveCenterY1, positiveCenterTangencyCell, E_t, hEt,
        globalDelta] using hq
    obtain ⟨i, hi⟩ := hactivePayload q hqPositive
    refine ⟨i, ?_⟩
    simpa only [Y1, actualCenteredHalfPaperFineY1, positiveCenterY1,
      positiveCenterTangencyCell, E_t, hEt, globalDelta] using hi
  · intro q i hi
    rw [hshading] at hi
    have hiY1 : i ∈ (actualProjectedCenteredHalfTangencyY1 E_t hEt
        D.S.family D.physical D.f D.f1 D.f2 D.outerA D.outerB D.hOuter
          D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
            D.tangencyExponent globalDelta).activeAtPoint q := by
      simpa only [Y1, actualCenteredHalfPaperFineY1] using hi
    exact (mem_actualProjectedCenteredHalfTangencyY1_data E_t hEt
      D.S.family D.physical D.f D.f1 D.f2 D.outerA D.outerB D.hOuter
        D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
          D.tangencyExponent globalDelta q i hiY1).1
  · intro q i hi
    rw [hshading] at hi
    rw [positiveCenterHighPayloadGlobalNormData_family]
    have hiY1 : i ∈ (actualProjectedCenteredHalfTangencyY1 E_t hEt
        D.S.family D.physical D.f D.f1 D.f2 D.outerA D.outerB D.hOuter
          D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
            D.tangencyExponent globalDelta).activeAtPoint q := by
      simpa only [Y1, actualCenteredHalfPaperFineY1] using hi
    exact (actualCenteredHalfY1_active_mem_globalNormFamilies E_t hEt
      D.S.family D.physical D.f D.f1 D.f2 D.outerA D.outerB D.hOuter
        D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
          D.tangencyExponent globalDelta q i hiY1).1

noncomputable def nativeHighActivePatternOccurrenceWeight
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (i : iota) : ENNReal :=
  (nativeHighActivePatternOccurrenceData D G c).occurrenceWeight i

theorem sum_nativeHighActivePatternOccurrenceWeight_eq_source
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    (∑ i ∈ (nativeHighFirstHitNormData D c).family,
      nativeHighActivePatternOccurrenceWeight D G c i) =
      volume (nativeHighActivePatternSource D G c) := by
  exact sum_occurrenceWeight_eq_source
    (nativeHighActivePatternOccurrenceData D G c)

/-- The arbitrary-weight proxy input synchronized with the pattern-first
occurrence weight. -/
noncomputable def nativeHighActivePatternProxyInput
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : NativeHighArbitraryWeightedProxyInput D where
  geometry := G
  center := c
  weight := nativeHighActivePatternOccurrenceWeight D G c

theorem nativeHighActivePattern_occurrence_mem_physicalAt
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (p : (nativeHighActivePatternOccurrenceData D G c).PatternIndex)
    {i : iota}
    (hi : i ∈
      (nativeHighActivePatternOccurrenceData D G c).occurrenceFiber p)
    {x : Real × Real}
    (hx : x ∈ activePatternEvent D.physical
      (nativeHighActivePatternSource D G c) p.1) :
    i ∈ D.physical.activeAtPoint x := by
  exact occurrence_mem_physicalAt_of_mem_event
    (nativeHighActivePatternOccurrenceData D G c) p hi hx

#print axioms nativeHighActivePatternSource
#print axioms nativeHighActivePatternOccurrenceData
#print axioms nativeHighActivePatternOccurrenceWeight
#print axioms sum_nativeHighActivePatternOccurrenceWeight_eq_source
#print axioms nativeHighActivePatternProxyInput
#print axioms nativeHighActivePattern_occurrence_mem_physicalAt

end

end Family8Family7NativeHighActivePatternOccurrenceProducerV1
