import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# Proposition 6.6(A) with a genuine uniform-count loss, V3

The exact scalar identity uses
`totalCount = plankCount * tubesPerPlank`.  A dyadically uniform family
naturally supplies only the reverse comparison
`plankCount * tubesPerPlank <= countLoss * totalCount`.  This file records
the corresponding honest loss `countLoss^(1-beta/2)` instead of requiring an
artificial exact cardinality equality.

V1 and V2 are failed multiplication-orientation drafts and are not imported.
-/

open scoped ENNReal NNReal

namespace Family8Prop66AUniformCountLossAlgebraV3

open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- Monotonicity of the Proposition 6.6(A) scalar under a multiplicative
upper comparison of the cardinality parameter. -/
theorem proposition66AFrostmanFactor_le_countLoss_mul
    {delta a b : NNReal} {approxCount totalCount : Nat}
    {CF countLoss : ENNReal} {epsilon beta : Real}
    (hbetaTwo : beta ≤ 2)
    (hcount : (approxCount : ENNReal) ≤
      countLoss * (totalCount : ENNReal)) :
    proposition66AFrostmanFactor delta a b approxCount CF epsilon beta ≤
      countLoss ^ (1 - beta / 2) *
        proposition66AFrostmanFactor delta a b totalCount CF epsilon beta := by
  have hp : 0 ≤ 1 - beta / 2 := by linarith
  have hcard :
      proposition66ACardScaleVolume delta approxCount ≤
        countLoss * proposition66ACardScaleVolume delta totalCount := by
    unfold proposition66ACardScaleVolume
    calc
      (delta : ENNReal) ^ (2 : Nat) * (approxCount : ENNReal) ≤
          (delta : ENNReal) ^ (2 : Nat) *
            (countLoss * (totalCount : ENNReal)) :=
        mul_le_mul' le_rfl hcount
      _ = countLoss *
          ((delta : ENNReal) ^ (2 : Nat) * (totalCount : ENNReal)) := by
        ac_rfl
  have hcardPow :
      proposition66ACardScaleVolume delta approxCount ^ (1 - beta / 2) ≤
        (countLoss * proposition66ACardScaleVolume delta totalCount) ^
          (1 - beta / 2) :=
    ENNReal.rpow_le_rpow hcard hp
  unfold proposition66AFrostmanFactor
  calc
    (delta : ENNReal) ^ (-epsilon) * CF ^ (1 - beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) *
          (delta : ENNReal) ^ (-2 * beta) *
          proposition66ACardScaleVolume delta approxCount ^
            (1 - beta / 2) ≤
        (delta : ENNReal) ^ (-epsilon) * CF ^ (1 - beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) *
          (delta : ENNReal) ^ (-2 * beta) *
          (countLoss * proposition66ACardScaleVolume delta totalCount) ^
            (1 - beta / 2) :=
      mul_le_mul' le_rfl hcardPow
    _ = countLoss ^ (1 - beta / 2) *
        ((delta : ENNReal) ^ (-epsilon) * CF ^ (1 - beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) *
          (delta : ENNReal) ^ (-2 * beta) *
          proposition66ACardScaleVolume delta totalCount ^
            (1 - beta / 2)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
      ac_rfl

/-- Product form used after the outer and inner Lemma 6.4 estimates. -/
theorem proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor
    {delta a b : NNReal} {plankCount tubesPerPlank totalCount : Nat}
    {CF countLoss : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) ≤
      countLoss * (totalCount : ENNReal)) :
    proposition66AOuterFactor delta a b plankCount CF epsilon beta *
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta ≤
      countLoss ^ (1 - beta / 2) *
        proposition66AFrostmanFactor delta a b totalCount CF epsilon beta := by
  rw [proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor
    hdelta ha hb hbeta hbetaOne rfl]
  exact proposition66AFrostmanFactor_le_countLoss_mul
    (hbetaOne.trans (by norm_num)) hcount

#print axioms proposition66AFrostmanFactor_le_countLoss_mul
#print axioms
  proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor

end
end Family8Prop66AUniformCountLossAlgebraV3
