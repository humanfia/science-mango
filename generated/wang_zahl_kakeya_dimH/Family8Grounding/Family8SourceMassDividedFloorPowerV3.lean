import Mathlib.Tactic

/-!
# Absorbing an exact divided source floor into a power bound, V3

V1 used invalid notation and V2 left the natural-cap coercion ambiguous;
neither is imported.  The small Frostman exponent remains explicit in the
budget, so this lemma cannot accidentally replace it by an unrelated source
exponent.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8SourceMassDividedFloorPowerV3

noncomputable section

/-- A divided power floor and a power upper bound for its finite denominator
give the desired source-mass power floor. -/
theorem sourceMass_power_of_divided_floor_and_cap_power
    {delta : NNReal} {cap mass : ENNReal}
    {etaSmall capExponent etaMass : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hcap0 : cap ≠ 0) (hcapTop : cap ≠ ∞)
    (hfloor : (delta : ENNReal) ^ (2 * etaSmall) / cap <= mass)
    (hcap : cap <= (delta : ENNReal) ^ (-capExponent))
    (hbudget : 2 * etaSmall + capExponent <= 2 * etaMass) :
    (delta : ENNReal) ^ (2 * etaMass) <= mass := by
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOne
  have hcross :
      (delta : ENNReal) ^ (2 * etaMass) * cap <=
        (delta : ENNReal) ^ (2 * etaSmall) := by
    calc
      (delta : ENNReal) ^ (2 * etaMass) * cap <=
          (delta : ENNReal) ^ (2 * etaMass) *
            (delta : ENNReal) ^ (-capExponent) :=
        mul_le_mul' le_rfl hcap
      _ = (delta : ENNReal) ^ (2 * etaMass - capExponent) := by
        rw [show 2 * etaMass - capExponent =
          2 * etaMass + (-capExponent) by ring,
          ENNReal.rpow_add _ _ hd0 hdTop]
      _ <= (delta : ENNReal) ^ (2 * etaSmall) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN (by linarith)
  have hdiv : (delta : ENNReal) ^ (2 * etaMass) <=
      (delta : ENNReal) ^ (2 * etaSmall) / cap := by
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl hcap0) (Or.inl hcapTop)).2 hcross
  exact hdiv.trans hfloor

/-- Natural-cap specialization used by the literal source-to-`tau` cap. -/
theorem sourceMass_power_of_divided_floor_and_natCap_power
    {delta : NNReal} {cap : Nat} {mass : ENNReal}
    {etaSmall capExponent etaMass : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hcapPos : 0 < cap)
    (hfloor : (delta : ENNReal) ^ (2 * etaSmall) /
      (cap : ENNReal) <= mass)
    (hcap : (cap : ENNReal) <=
      (delta : ENNReal) ^ (-capExponent))
    (hbudget : 2 * etaSmall + capExponent <= 2 * etaMass) :
    (delta : ENNReal) ^ (2 * etaMass) <= mass := by
  apply sourceMass_power_of_divided_floor_and_cap_power
    (cap := (cap : ENNReal)) hdelta hdeltaOne
  · exact_mod_cast (Nat.ne_of_gt hcapPos)
  · exact ENNReal.coe_ne_top
  · exact hfloor
  · exact hcap
  · exact hbudget

#print axioms sourceMass_power_of_divided_floor_and_cap_power
#print axioms sourceMass_power_of_divided_floor_and_natCap_power

end

end Family8SourceMassDividedFloorPowerV3
