import Family8Grounding.Family8Family7GenericNativeHighOccurrenceDefinitionsV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternSourceSubsetV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! The active-pattern source is the literal `E2` selected inside the
high-centre base.  V1 and V2 omitted namespaces required by the payload API
and are not imported. -/

theorem genericNativeHighActivePatternSource_subset_highBase
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    genericNativeHighActivePatternSource D G c ⊆ D.highBase c := by
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) S.family physical
    f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) S.family physical
      f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    S.family physical H.payload.finalLabel (G.mesh c) f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  let Y1 := actualCenteredHalfPaperFineY1 E_t hEt S.family physical
    f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 (36 * D.globalScale) D.tangencyExponent globalDelta
  have hshading : R.shading = Y1 := by rfl
  obtain ⟨_hlabel, _hq, _hmass, _hEtPos, hEtSubset, _hbin,
      _hE2Pos, _hE2Measurable, hE2Subset, _hactivePayload⟩ :=
    H.payload.certificate
  intro q hq
  have hqE2 : q ∈ positiveCenterE2 (D.highBase c)
      (D.highBase_measurable c) S.family physical f D.f1 D.f2
        D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
          D.tangencyExponent H.payload.tangencyLabel
            H.payload.finalLabel := by
    change q ∈ projectedPositiveMultiplicityDyadicCell
      R.shading H.payload.finalLabel at hq
    rw [hshading] at hq
    simpa only [Y1, actualCenteredHalfPaperFineY1, positiveCenterE2,
      positiveCenterY1, positiveCenterTangencyCell, E_t, hEt,
      globalDelta] using hq
  exact hEtSubset (hE2Subset hqE2)

#print axioms genericNativeHighActivePatternSource_subset_highBase

end
end Family8Family7GenericNativeHighActivePatternSourceSubsetV3
