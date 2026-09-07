import Family8Grounding.Family8Family7GenericNativeHighOccurrenceSourceRetentionSumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighPositiveOccurrenceCenterV1

open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceSourceRetentionSumV1
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

/-! # A genuine positive active-pattern source in the high-mass branch -/

theorem exists_positive_genericNativeHighActivePatternSource
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D)
    (hsource : 0 < D.sourceMass)
    (hhalf : D.sourceMass / 2 ≤
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    ∃ c : D.HighCenter,
      0 < volume (genericNativeHighActivePatternSource D G c) := by
  have hhalfPos : 0 < D.sourceMass / 2 :=
    ENNReal.div_pos hsource.ne' (by norm_num)
  have hproductPos :
      0 < actualAllCenterPostNormBinLoss radius D.globalScale
          physical.ambient.card *
        ∑ c : D.HighCenter,
          volume (genericNativeHighActivePatternSource D G c) :=
    hhalfPos.trans_le
      (sourceMass_half_le_postNormBinLoss_mul_sum_genericActivePatternSource
        D G hhalf)
  have hsumPos : 0 < ∑ c : D.HighCenter,
      volume (genericNativeHighActivePatternSource D G c) :=
    (ENNReal.mul_pos_iff.mp hproductPos).2
  rw [Finset.sum_pos_iff] at hsumPos
  obtain ⟨c, _hc, hcPos⟩ := hsumPos
  exact ⟨c, hcPos⟩

#print axioms exists_positive_genericNativeHighActivePatternSource

end

end Family8Family7GenericNativeHighPositiveOccurrenceCenterV1
