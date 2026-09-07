import Family8Grounding.Family8ShadingAwareSelectionLossPowerV1
import Mathlib.Tactic

/-!
# Power absorption for both fixed factors in shading-aware selection

Besides the weighted logarithmic selection loss, the exact dyadic partition
has literal branching loss `2`.  This file absorbs that second fixed factor
without charging a source-card power.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ShadingAwareSelectionBranchLossPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ShadingAwareSelectionLossPowerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

def shadingAwareSelectionBranchLossPowerThreshold (lossEta : Real) : NNReal :=
  min (shadingAwareSelectionLossPowerThreshold (lossEta / 2))
    (finiteConstantSmallDeltaThreshold (2 : ENNReal) (lossEta / 2))

theorem shadingAwareSelectionBranchLossPowerThreshold_pos (lossEta : Real) :
    0 < shadingAwareSelectionBranchLossPowerThreshold lossEta := by
  unfold shadingAwareSelectionBranchLossPowerThreshold
  exact lt_min (shadingAwareSelectionLossPowerThreshold_pos _)
    (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The logarithmic selection loss times the partition's literal branching
loss `2` is bounded by one prescribed power. -/
theorem shadingAwareSelectionBranchLoss_le_delta_negativePower
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta <=
      shadingAwareSelectionBranchLossPowerThreshold lossEta) :
    ((2 * (2 * (Nat.log 2 (Fintype.card index) + 1)) : Nat) : ENNReal) <=
      (delta : ENNReal) ^ (-lossEta) := by
  have hhalf : 0 < lossEta / 2 := by positivity
  have hselection :
      ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) <=
        (delta : ENNReal) ^ (-(lossEta / 2)) :=
    shadingAwareSelectionLoss_le_delta_negativePower D hD hhalf
      (hdelta.trans (min_le_left _ _))
  have htwo : (2 : ENNReal) <=
      (delta : ENNReal) ^ (-(lossEta / 2)) :=
    finiteConstant_le_delta_negativePower (by norm_num) hhalf hD.delta_pos
      (hdelta.trans (min_le_right _ _))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    ((2 * (2 * (Nat.log 2 (Fintype.card index) + 1)) : Nat) : ENNReal) =
        (2 : ENNReal) *
          ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) := by
            norm_num
    _ <= (delta : ENNReal) ^ (-(lossEta / 2)) *
        (delta : ENNReal) ^ (-(lossEta / 2)) := mul_le_mul' htwo hselection
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

#print axioms shadingAwareSelectionBranchLossPowerThreshold_pos
#print axioms shadingAwareSelectionBranchLoss_le_delta_negativePower

end
end Family8ShadingAwareSelectionBranchLossPowerV1
