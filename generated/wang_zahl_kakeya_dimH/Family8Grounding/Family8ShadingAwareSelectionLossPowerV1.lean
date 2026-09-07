import Family8Grounding.Family8FrozenComparableLogLossSourceCardTransferV2
import Mathlib.Tactic

/-!
# Power absorption for the shading-aware logarithmic selection loss

Admissibility bounds the ambient source cardinality by a fixed multiple of
`delta ^ (-4)`.  Since the shading-aware selector loses only
`2 * (log_2(card index) + 1)`, that loss is bounded by an arbitrarily small
negative power of `delta`, after an explicit uniform small-scale threshold.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open scoped ENNReal NNReal

namespace Family8ShadingAwareSelectionLossPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8FrozenComparableLogLossSourceCardTransferV2
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- A uniform threshold absorbing both the single-log real coefficient and
the literal leading factor `2`. -/
def shadingAwareSelectionLossPowerThreshold (lossEta : Real) : NNReal :=
  min (1 / 100 : NNReal)
    (finiteConstantSmallDeltaThreshold
      ((2 : ENNReal) * ENNReal.ofReal
        (activeFrozenLogFactorConstant (2 * lossEta)))
      (lossEta / 2))

theorem shadingAwareSelectionLossPowerThreshold_pos (lossEta : Real) :
    0 < shadingAwareSelectionLossPowerThreshold lossEta := by
  unfold shadingAwareSelectionLossPowerThreshold
  exact lt_min (by norm_num) (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The actual finite loss of the shading-aware logarithmic selector costs
at most the prescribed power of the source scale. -/
theorem shadingAwareSelectionLoss_le_delta_negativePower
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta <= shadingAwareSelectionLossPowerThreshold lossEta) :
    ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) <=
      (delta : ENNReal) ^ (-lossEta) := by
  have hdeltaSmall : delta <= (1 / 100 : NNReal) :=
    hdelta.trans (min_le_left _ _)
  have hdeltaOne : delta <= 1 :=
    hdeltaSmall.trans (div_le_one_of_le₀ (by norm_num) (by positivity))
  have hsource := sourceIndexCard_real_le_sourcePower D hD hdeltaSmall
  have htwoloss : 0 < 2 * lossEta := by positivity
  have hlogRaw := natLogFactor_real_le hD.delta_pos hdeltaOne
    htwoloss hsource
  have hlog :
      ((Nat.log 2 (Fintype.card index) + 2 : Nat) : Real) <=
        activeFrozenLogFactorConstant (2 * lossEta) *
          (delta : Real) ^ (-(lossEta / 2)) := by
    convert hlogRaw using 1
    ring
  have hselectionReal :
      ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : Real) <=
        (2 * activeFrozenLogFactorConstant (2 * lossEta)) *
          (delta : Real) ^ (-(lossEta / 2)) := by
    calc
      ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : Real) =
          2 * ((Nat.log 2 (Fintype.card index) + 1 : Nat) : Real) := by
            norm_num
      _ <= 2 * ((Nat.log 2 (Fintype.card index) + 2 : Nat) : Real) := by
        gcongr
        norm_num
      _ <= 2 * (activeFrozenLogFactorConstant (2 * lossEta) *
          (delta : Real) ^ (-(lossEta / 2))) := by
        exact mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ = (2 * activeFrozenLogFactorConstant (2 * lossEta)) *
          (delta : Real) ^ (-(lossEta / 2)) := by ring
  let K : ENNReal := (2 : ENNReal) * ENNReal.ofReal
    (activeFrozenLogFactorConstant (2 * lossEta))
  have hfactorNonneg :
      0 <= activeFrozenLogFactorConstant (2 * lossEta) :=
    (activeFrozenLogFactorConstant_pos htwoloss).le
  have hKFinite : K ≠ ∞ := by
    dsimp only [K]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have hhalf : 0 < lossEta / 2 := by positivity
  have hK : K <= (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact finiteConstant_le_delta_negativePower hKFinite hhalf hD.delta_pos
      (hdelta.trans (min_le_right _ _))
  have hpre :
      ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) <=
        K * (delta : ENNReal) ^ (-(lossEta / 2)) := by
    have hdeltaReal : 0 < (delta : Real) := by
      exact_mod_cast hD.delta_pos
    rw [<- ENNReal.ofReal_natCast]
    rw [show (delta : ENNReal) ^ (-(lossEta / 2)) =
        ENNReal.ofReal ((delta : Real) ^ (-(lossEta / 2))) by
      simpa using ENNReal.ofReal_rpow_of_pos hdeltaReal]
    rw [show K = ENNReal.ofReal
        (2 * activeFrozenLogFactorConstant (2 * lossEta)) by
      dsimp only [K]
      rw [ENNReal.ofReal_mul (by norm_num : 0 <= (2 : Real))]
      norm_num]
    rw [<- ENNReal.ofReal_mul
      (mul_nonneg (by norm_num) hfactorNonneg)]
    exact ENNReal.ofReal_le_ofReal hselectionReal
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) <=
        K * (delta : ENNReal) ^ (-(lossEta / 2)) := hpre
    _ <= (delta : ENNReal) ^ (-(lossEta / 2)) *
        (delta : ENNReal) ^ (-(lossEta / 2)) := mul_le_mul' hK le_rfl
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

#print axioms shadingAwareSelectionLossPowerThreshold_pos
#print axioms shadingAwareSelectionLoss_le_delta_negativePower

end
end Family8ShadingAwareSelectionLossPowerV1
