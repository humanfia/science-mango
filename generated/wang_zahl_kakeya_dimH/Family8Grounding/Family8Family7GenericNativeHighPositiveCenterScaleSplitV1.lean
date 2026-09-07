import Family8Grounding.Family8Family7GenericNativeHighPositiveOccurrenceCenterV1
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceScaleSplitV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighPositiveCenterScaleSplitV1

open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighPositiveOccurrenceCenterV1
open Family8Family7GenericNativeHighOccurrenceCriticalScalePositiveV1
open Family8Family7GenericNativeHighOccurrenceScaleSplitV1
open Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-! # A positive high-center on the honest native scale split -/

theorem exists_positive_genericNativeHighActivePattern_scaleSplit
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D)
    (hsource : 0 < D.sourceMass)
    (hhalf : D.sourceMass / 2 ≤
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    ∃ c : D.HighCenter,
      0 < volume (genericNativeHighActivePatternSource D G c) ∧
      ((genericNativeHighActivePatternWeightedNormData D G c).criticalScale <
          10 * G.ballRadius c ∨
        criticalScaleProxyRadius radius
            (genericNativeHighActivePatternWeightedNormData D G c).criticalScale
            (genericNativeHighActivePatternCriticalScale_pos D G c) ≤
          (1 / 5 : NNReal)) := by
  obtain ⟨c, hc⟩ :=
    exists_positive_genericNativeHighActivePatternSource D G hsource hhalf
  exact ⟨c, hc,
    genericNativeHighActivePattern_scaleRestart_or_proxyRadius_le_one_fifth
      D G c⟩

#print axioms
  exists_positive_genericNativeHighActivePattern_scaleSplit

end

end Family8Family7GenericNativeHighPositiveCenterScaleSplitV1
