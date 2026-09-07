import Family8Grounding.Family8Family7GenericNativeHighOccurrenceSourceRetentionPointwiseV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighOccurrenceSourceRetentionSumV1

open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceSourceRetentionPointwiseV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-!
# Quantitative generic native-high E2 retention

The genuine high alternative of `payloadAt_spec` and the pointwise payload
certificate retain half of the generic source in the sum of literal E2
active-pattern sources, up to only the existing post-norm bin loss.
-/

theorem sourceMass_half_le_postNormBinLoss_mul_sum_genericActivePatternSource
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D)
    (hhalf : D.sourceMass / 2 ≤
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 2 ≤
      actualAllCenterPostNormBinLoss radius D.globalScale
          physical.ambient.card *
        ∑ c : D.HighCenter,
          volume (genericNativeHighActivePatternSource D G c) := by
  classical
  have hbaseSum :
      (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := by
    simpa only [GenericNativeBranchCore.highBase,
      GenericNativeBranchCore.positiveBase, Finset.univ_eq_attach] using
        Finset.sum_attach D.high (fun c => volume (D.cell c.1))
  calc
    D.sourceMass / 2 ≤
        ∑ c : D.HighCenter, volume (D.highBase c) :=
      hhalf.trans_eq hbaseSum.symm
    _ ≤ ∑ c : D.HighCenter,
        actualAllCenterPostNormBinLoss radius D.globalScale
            physical.ambient.card *
          volume (genericNativeHighActivePatternSource D G c) := by
      exact Finset.sum_le_sum fun c _hc =>
        highBase_le_postNormBinLoss_mul_genericActivePatternSource D G c
    _ = actualAllCenterPostNormBinLoss radius D.globalScale
          physical.ambient.card *
        ∑ c : D.HighCenter,
          volume (genericNativeHighActivePatternSource D G c) := by
      rw [Finset.mul_sum]

#print axioms
  sourceMass_half_le_postNormBinLoss_mul_sum_genericActivePatternSource

end

end Family8Family7GenericNativeHighOccurrenceSourceRetentionSumV1
