import Mathlib.Tactic

/-!
# Fourth-scale cancellation against a card-scale power envelope, V3

V1 and V2 are failed drafts and are not imported.  This proof-only scalar
lemma records the exact exponent budget needed to turn `b <= delta^s` and
`X <= delta^(-A)` into `b^4 X <= 1`.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FourthCardScalePowerCancellationV3

noncomputable section

/-- Four copies of the positive absolute scale absorb a negative card-scale
power whenever `A <= 4s`. -/
theorem fourth_mul_cardScale_le_one_of_power
    {delta : NNReal} {b X : ENNReal} {scaleExponent cardExponent : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hb : b <= (delta : ENNReal) ^ scaleExponent)
    (hX : X <= (delta : ENNReal) ^ (-cardExponent))
    (hbudget : cardExponent <= 4 * scaleExponent) :
    b ^ (4 : Nat) * X <= 1 := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : (delta : ENNReal) <= 1 := by exact_mod_cast hdeltaOne
  have hbFourth :
      b ^ (4 : Nat) <= (delta : ENNReal) ^ (4 * scaleExponent) := by
    rw [← ENNReal.rpow_natCast]
    calc
      b ^ (4 : Real) <=
          ((delta : ENNReal) ^ scaleExponent) ^ (4 : Real) :=
        ENNReal.rpow_le_rpow hb (by norm_num)
      _ = (delta : ENNReal) ^ (scaleExponent * 4) :=
        (ENNReal.rpow_mul _ _ _).symm
      _ = (delta : ENNReal) ^ (4 * scaleExponent) := by
        congr 1
        ring
  calc
    b ^ (4 : Nat) * X <=
        (delta : ENNReal) ^ (4 * scaleExponent) *
          (delta : ENNReal) ^ (-cardExponent) :=
      mul_le_mul' hbFourth hX
    _ = (delta : ENNReal) ^ (4 * scaleExponent - cardExponent) := by
      rw [show 4 * scaleExponent - cardExponent =
          4 * scaleExponent + (-cardExponent) by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= 1 := ENNReal.rpow_le_one hdOne (by linarith)

#print axioms fourth_mul_cardScale_le_one_of_power

end
end Family8FourthCardScalePowerCancellationV3
