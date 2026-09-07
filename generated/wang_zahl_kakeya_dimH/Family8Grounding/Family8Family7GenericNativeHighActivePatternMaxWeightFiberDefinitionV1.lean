import Family8Grounding.Family8FiniteENNRealMaxWeightFiberV1
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1

open Family8FiniteENNRealMaxWeightFiberV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- The literal positive-candidate equal-weight fibre used before the
restricted weighted critical-scale choice.  Positivity and quantitative
retention are proved separately, so this definition has no conclusion-valued
field. -/
noncomputable def genericNativeHighActivePatternMaxWeightFiber
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) : Finset iota :=
  maxWeightFiber
    (genericNativeHighFirstHitNormData D c).family
    (genericNativeHighActivePatternOccurrenceWeight D G c)
    (genericNativeHighFirstHitNormData D c).family_nonempty

end

end Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1
