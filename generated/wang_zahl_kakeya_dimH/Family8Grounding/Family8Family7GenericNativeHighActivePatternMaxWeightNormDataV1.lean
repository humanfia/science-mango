import Family8Grounding.Family8Family7GenericNativeHighRestrictedWeightedNormDataV1
import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightFiberNonemptyV3
import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightFiberSubsetV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1

open Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1
open Family8Family7GenericNativeHighActivePatternMaxWeightFiberNonemptyV3
open Family8Family7GenericNativeHighActivePatternMaxWeightFiberSubsetV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8Family7GenericNativeHighRestrictedWeightedNormDataV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- The weighted canonical datum restricted to the literal positive
maximal-occurrence-weight fibre.  Its metric and scale parameters are exactly
those of the fixed high-centre norm datum. -/
noncomputable def genericNativeHighActivePatternMaxWeightNormData
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0) :
    WeightedCanonicalNormBallData iota :=
  genericNativeHighRestrictedWeightedNormData D c
    (genericNativeHighActivePatternOccurrenceWeight D G c)
    (genericNativeHighActivePatternMaxWeightFiber D G c)
    (genericNativeHighActivePatternMaxWeightFiber_nonempty D G c hsource)
    (genericNativeHighActivePatternMaxWeightFiber_subset D G c)

end

end Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
