import Family8Grounding.Family8Family7GenericNativeHighOccurrenceDefinitionsV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighOccurrenceSourceRetentionPointwiseV1

open Submission.Kakeya.ConvexGeometry
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-!
# Pointwise E2 source retention for the generic native-high route

The canonical payload certificate already contains this estimate.  This
successor only identifies its literal E2 with the generic active-pattern
source; no mass callback is introduced.
-/

theorem highBase_le_postNormBinLoss_mul_genericActivePatternSource
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    volume (D.highBase c) ≤
      actualAllCenterPostNormBinLoss radius D.globalScale
          physical.ambient.card *
        volume (genericNativeHighActivePatternSource D G c) := by
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) S.family physical
    f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let Y1 := positiveCenterY1 (D.highBase c) (D.highBase_measurable c)
    S.family physical f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
      D.globalScale c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let E2 := positiveCenterE2 (D.highBase c) (D.highBase_measurable c)
    S.family physical f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
      D.globalScale c.1.1 D.tangencyExponent H.payload.tangencyLabel
        H.payload.finalLabel
  obtain ⟨_hlabel, _hq, hmass, _hEtPos, _hEtSubset, _hbin,
      _hE2Pos, _hE2Measurable, _hE2Subset, _hactive⟩ :=
    H.payload.certificate
  have hsource : genericNativeHighActivePatternSource D G c = E2 := by
    rfl
  rw [hsource]
  simpa only [E_t, Y1, E2, H] using hmass

#print axioms highBase_le_postNormBinLoss_mul_genericActivePatternSource

end

end Family8Family7GenericNativeHighOccurrenceSourceRetentionPointwiseV1
