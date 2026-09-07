import Family8Grounding.Family8Family7ActivePatternOccurrenceWeightV1
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceDefinitionsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternOccurrenceDataV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7ActivePatternOccurrenceWeightV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-!
# Generic native-high active-pattern occurrence datum

This file contains only the dependent producer theorem.  Weight projections
and weighted critical-ball constructions live in successors so that Lean
does not re-elaborate the whole result in one declaration unit.
-/

/-- Exact physical-pattern partition of the generic high-centre E2 source. -/
theorem genericNativeHighActivePatternOccurrenceData
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    ActivePatternOccurrenceData (genericNativeHighFirstHitNormData D c)
      physical (genericNativeHighFirstHitIncidenceData D G c).shading
      (genericNativeHighActivePatternSource D G c) := by
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) S.family physical
    f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) S.family physical
      f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let N := positiveCenterHighPayloadGlobalNormData H
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    S.family physical H.payload.finalLabel (G.mesh c) f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  let Y1 := actualCenteredHalfPaperFineY1 E_t hEt S.family physical
    f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 (36 * D.globalScale) D.tangencyExponent globalDelta
  change ActivePatternOccurrenceData N physical R.shading
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
        (D.highBase_measurable c) S.family physical f D.f1 D.f2
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
        S.family physical f D.f1 D.f2 D.outerA D.outerB D.hOuter
          D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
            D.tangencyExponent globalDelta).activeAtPoint q := by
      simpa only [Y1, actualCenteredHalfPaperFineY1] using hi
    exact (mem_actualProjectedCenteredHalfTangencyY1_data E_t hEt
      S.family physical f D.f1 D.f2 D.outerA D.outerB D.hOuter
        D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
          D.tangencyExponent globalDelta q i hiY1).1
  · intro q i hi
    rw [hshading] at hi
    rw [positiveCenterHighPayloadGlobalNormData_family]
    have hiY1 : i ∈ (actualProjectedCenteredHalfTangencyY1 E_t hEt
        S.family physical f D.f1 D.f2 D.outerA D.outerB D.hOuter
          D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
            D.tangencyExponent globalDelta).activeAtPoint q := by
      simpa only [Y1, actualCenteredHalfPaperFineY1] using hi
    exact (actualCenteredHalfY1_active_mem_globalNormFamilies E_t hEt
      S.family physical f D.f1 D.f2 D.outerA D.outerB D.hOuter
        D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
          D.tangencyExponent globalDelta q i hiY1).1

#print axioms genericNativeHighActivePatternOccurrenceData

end

end Family8Family7GenericNativeHighActivePatternOccurrenceDataV1
