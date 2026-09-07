import Family8Grounding.Family8Family7GenericNativeHighOccurrenceScaleSplitV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped NNReal

namespace Family8Family7GenericNativeHighBetaOuterScaleUnionV1

open Family8Family7GenericNativeHighGeometryV1
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

/-!
# Honest beta outer union for the generic native-high route

The strict small-beta side is exactly the range of the adaptive-power
residual.  On its complement this theorem exposes the native scale split,
without pretending that the small critical-scale inequality is already a
`FirstActualNormalizedCrossingWitness` or `DividingScaleOutput`.
-/

theorem beta_lt_two_thirds_or_largeBeta_nativeScaleSplit
    (beta : Real)
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    beta < (2 / 3 : Real) ∨
      ((2 / 3 : Real) ≤ beta ∧
        ((genericNativeHighActivePatternWeightedNormData D G c).criticalScale <
            10 * G.ballRadius c ∨
          criticalScaleProxyRadius radius
              (genericNativeHighActivePatternWeightedNormData D G c).criticalScale
              (genericNativeHighActivePatternCriticalScale_pos D G c) ≤
            (1 / 5 : NNReal))) := by
  by_cases hbeta : beta < (2 / 3 : Real)
  · exact Or.inl hbeta
  · exact Or.inr ⟨le_of_not_gt hbeta,
      genericNativeHighActivePattern_scaleRestart_or_proxyRadius_le_one_fifth
        D G c⟩

#print axioms beta_lt_two_thirds_or_largeBeta_nativeScaleSplit

end

end Family8Family7GenericNativeHighBetaOuterScaleUnionV1
