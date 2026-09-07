import Family8Grounding.Family8WeightedCanonicalEqualWeightCardRatioV2
import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightNormCommonV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternMaxWeightCardRatioV1

open Family8Family7GenericNativeHighActivePatternMaxWeightNormCommonV1
open Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
open Family8Family7GenericNativeHighActivePatternMaxWeightValueV2
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8WeightedCanonicalEqualWeightCardRatioV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- Literal cardinal nonconcentration for the restricted active-pattern
maximal-weight critical ball.  The two source-mass conditions are genuine
measure facts, not target inequalities. -/
theorem genericNativeHighActivePatternMaxWeight_ballCard_le
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0)
    (hsourceTop : volume (genericNativeHighActivePatternSource D G c) ≠ ∞)
    {testRadius : Real}
    (hradiusLower :
      (genericNativeHighActivePatternMaxWeightNormData D G c hsource).delta ≤
        testRadius)
    (hradiusUpper : testRadius ≤
      (genericNativeHighActivePatternMaxWeightNormData D G c hsource).ceiling)
    (testCenter : iota)
    (htestCenter : testCenter ∈
      (genericNativeHighActivePatternMaxWeightNormData D G c hsource).family) :
    let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
    ((W.family.filter fun i => W.distance i testCenter ≤ testRadius).card :
        ENNReal) ≤
      ((ENNReal.ofReal testRadius) / ENNReal.ofReal W.criticalScale) ^
          W.exponent *
        (W.criticalBall.card : ENNReal) := by
  let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
  exact ballCard_le_ratio_rpow_mul_criticalBallCard W
    (genericNativeHighActivePatternMaxWeightValue D G c)
    (genericNativeHighActivePatternMaxWeightNormData_common D G c hsource)
    (genericNativeHighActivePatternMaxWeightValue_ne_zero D G c hsource)
    (genericNativeHighActivePatternMaxWeightValue_ne_top D G c hsourceTop)
    hradiusLower hradiusUpper testCenter htestCenter

end

end Family8Family7GenericNativeHighActivePatternMaxWeightCardRatioV1
