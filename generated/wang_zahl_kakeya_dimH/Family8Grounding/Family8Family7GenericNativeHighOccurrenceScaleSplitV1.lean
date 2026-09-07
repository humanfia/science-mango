import Family8Grounding.Family8Family7GenericNativeHighOccurrenceCriticalScalePositiveV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open scoped NNReal

namespace Family8Family7GenericNativeHighOccurrenceScaleSplitV1

open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceCriticalScalePositiveV1
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

/-!
# Honest generic native-high scale split

The small side is deliberately only the literal weighted critical-scale
inequality.  It is not mislabeled as a normalized first-crossing witness.
The large side has the genuine `1/5` affine-proxy radius cap.
-/

theorem genericNativeHighActivePattern_scaleRestart_or_proxyRadius_le_one_fifth
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    (genericNativeHighActivePatternWeightedNormData D G c).criticalScale <
        10 * G.ballRadius c ∨
      criticalScaleProxyRadius radius
          (genericNativeHighActivePatternWeightedNormData D G c).criticalScale
          (genericNativeHighActivePatternCriticalScale_pos D G c) ≤
        (1 / 5 : NNReal) := by
  by_cases hscale :
      (genericNativeHighActivePatternWeightedNormData D G c).criticalScale <
        10 * G.ballRadius c
  · exact Or.inl hscale
  · right
    apply criticalScaleProxyRadius_le_one_fifth
    have htenBall : 10 * G.ballRadius c ≤
        (genericNativeHighActivePatternWeightedNormData D G c).criticalScale :=
      le_of_not_gt hscale
    nlinarith [G.hballRadiusLower c]

#print axioms
  genericNativeHighActivePattern_scaleRestart_or_proxyRadius_le_one_fifth

end

end Family8Family7GenericNativeHighOccurrenceScaleSplitV1
