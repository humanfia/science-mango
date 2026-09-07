import Family8Grounding.Family8PlankThickControlRetainedOwnerFamilyV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8PlankRetainedOwnerLogCardPowerEnvelopeV1

noncomputable section

/-!
# A uniform power envelope for the retained-owner logarithmic loss

The retained-owner selection loses `log_2 n + 1`, where `n` is the original
index cardinality.  Unlike a data-dependent small-scale threshold, this loss
can be paid by an arbitrarily small positive power of `n`.  This is the
uniform form needed to combine it with a count power already present in the
Family 6 Frostman factor.
-/

def retainedOwnerLogPowerConstant (kappa : Real) : Real :=
  1 / kappa / Real.log 2 + 1

theorem retainedOwnerLogPowerConstant_pos
    {kappa : Real} (hkappa : 0 < kappa) :
    0 < retainedOwnerLogPowerConstant kappa := by
  unfold retainedOwnerLogPowerConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem natLog_add_one_real_le_card_rpow
    (n : Nat) {kappa : Real} (hn : 1 ≤ n) (hkappa : 0 < kappa) :
    ((Nat.log 2 n + 1 : Nat) : Real) ≤
      retainedOwnerLogPowerConstant kappa * (n : Real) ^ kappa := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnNonneg : 0 ≤ (n : Real) := by positivity
  have hnOne : (1 : Real) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_le_rpow_div hnNonneg hkappa
  have hlogb :
      Real.logb 2 n ≤ (n : Real) ^ kappa / kappa / Real.log 2 := by
    unfold Real.logb
    exact (div_le_div_iff_of_pos_right hlogTwo).2 hlog
  have hnatLog : (Nat.log 2 n : Real) ≤ Real.logb 2 n := by
    simpa using Real.natLog_le_logb n 2
  have hpowOne : 1 ≤ (n : Real) ^ kappa := by
    have h := Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : Real))
      hnOne hkappa.le
    simpa using h
  calc
    ((Nat.log 2 n + 1 : Nat) : Real) =
        (Nat.log 2 n : Real) + 1 := by norm_num
    _ ≤ Real.logb 2 n + 1 := by gcongr
    _ ≤ (n : Real) ^ kappa / kappa / Real.log 2 + 1 := by gcongr
    _ ≤ (n : Real) ^ kappa / kappa / Real.log 2 +
        (n : Real) ^ kappa := by gcongr
    _ = retainedOwnerLogPowerConstant kappa * (n : Real) ^ kappa := by
      unfold retainedOwnerLogPowerConstant
      ring

theorem natLog_add_one_ennreal_le_card_rpow
    (n : Nat) {kappa : Real} (hn : 1 ≤ n) (hkappa : 0 < kappa) :
    ((Nat.log 2 n + 1 : Nat) : ENNReal) ≤
      ENNReal.ofReal (retainedOwnerLogPowerConstant kappa) *
        (n : ENNReal) ^ kappa := by
  have hreal := natLog_add_one_real_le_card_rpow n hn hkappa
  have hconstant : 0 ≤ retainedOwnerLogPowerConstant kappa :=
    (retainedOwnerLogPowerConstant_pos hkappa).le
  have hnPos : 0 < (n : Real) := by
    exact_mod_cast (zero_lt_one.trans_le hn)
  rw [← ENNReal.ofReal_natCast]
  rw [show (n : ENNReal) ^ kappa =
      ENNReal.ofReal ((n : Real) ^ kappa) by
    simpa using ENNReal.ofReal_rpow_of_pos hnPos]
  rw [← ENNReal.ofReal_mul hconstant]
  exact ENNReal.ofReal_le_ofReal hreal

#print axioms retainedOwnerLogPowerConstant_pos
#print axioms natLog_add_one_real_le_card_rpow
#print axioms natLog_add_one_ennreal_le_card_rpow

end
end Family8PlankRetainedOwnerLogCardPowerEnvelopeV1
