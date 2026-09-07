import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternMaxWeightFiberSubsetV1

open Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- The maximal occurrence-weight fibre is a literal subfamily of the same
canonical norm family. -/
theorem genericNativeHighActivePatternMaxWeightFiber_subset
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    genericNativeHighActivePatternMaxWeightFiber D G c ⊆
      (genericNativeHighFirstHitNormData D c).family := by
  exact Finset.filter_subset _ _

end

end Family8Family7GenericNativeHighActivePatternMaxWeightFiberSubsetV1
