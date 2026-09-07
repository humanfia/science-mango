import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternProxyInputV1

open Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1
open Family8Family7GenericNativeHighWeightedNormDataV1
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

noncomputable def genericNativeHighActivePatternProxyInput
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    GenericNativeHighArbitraryWeightedProxyInput D where
  geometry := G
  center := c
  weight := genericNativeHighActivePatternOccurrenceWeight D G c

@[simp] theorem genericNativeHighActivePatternProxyInput_geometry
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    (genericNativeHighActivePatternProxyInput D G c).geometry = G :=
  rfl

@[simp] theorem genericNativeHighActivePatternProxyInput_center
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    (genericNativeHighActivePatternProxyInput D G c).center = c :=
  rfl

@[simp] theorem genericNativeHighActivePatternProxyInput_weight
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    (genericNativeHighActivePatternProxyInput D G c).weight =
      genericNativeHighActivePatternOccurrenceWeight D G c :=
  rfl

@[simp] theorem
    genericNativeHighWeightedNormData_activePatternProxyInput
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    genericNativeHighWeightedNormData D
        (genericNativeHighActivePatternProxyInput D G c).center
        (genericNativeHighActivePatternProxyInput D G c).weight =
      genericNativeHighActivePatternWeightedNormData D G c :=
  rfl

#print axioms genericNativeHighActivePatternProxyInput
#print axioms
  genericNativeHighWeightedNormData_activePatternProxyInput

end

end Family8Family7GenericNativeHighActivePatternProxyInputV1
