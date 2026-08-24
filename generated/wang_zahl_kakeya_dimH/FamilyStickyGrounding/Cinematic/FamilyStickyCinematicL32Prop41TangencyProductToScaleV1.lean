import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41TangencyProductToScaleV1

noncomputable section

/-!
# From the PYZ Lemma 3.9 product to a tangency-scale bound

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.9 and
the proof of Lemma 4.7.

This is the denominator-free numerical splice used when the curve-pair
coefficient distance is at least the rectangle scale.  It does not assume
the desired bound on the tangency parameter.
-/

/-- The fixed coefficient in the canonical-quarter Lemma 3.9 theorem. -/
def prop41TangencyProductCoefficient : Real :=
  (1 / 3600000 : Real) ^ 2

/-- The explicit scale-loss after applying Lemma 3.9 at sublevel tolerance
`q * delta` and auxiliary scale `q * t`. -/
def prop41TangencyScaleFactor (q : Real) : Real :=
  20000 * q ^ 2 / prop41TangencyProductCoefficient

theorem prop41TangencyProductCoefficient_pos :
    0 < prop41TangencyProductCoefficient := by
  norm_num [prop41TangencyProductCoefficient]

/-- The actual Lemma 3.9 product and `t <= coefficient` imply the required
linear upper bound for the canonical tangency parameter. -/
theorem tangency_le_prop41TangencyScaleFactor_mul_delta_of_product
    {delta t coefficient tangency q : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 0 < q)
    (hcoefficient : t <= coefficient)
    (hproduct :
      prop41TangencyProductCoefficient * (tangency + q * delta) *
          coefficient <=
        20000 * (q * delta) * (q * t)) :
    tangency <= prop41TangencyScaleFactor q * delta := by
  have hcoefficientPos : 0 < coefficient := lt_of_lt_of_le ht hcoefficient
  have hqdelta : 0 <= q * delta := by positivity
  have hright :
      20000 * (q * delta) * (q * t) <=
        (20000 * q ^ 2 * delta) * coefficient := by
    have hqt : q * t <= q * coefficient :=
      mul_le_mul_of_nonneg_left hcoefficient (le_of_lt hq)
    calc
      20000 * (q * delta) * (q * t) <=
          20000 * (q * delta) * (q * coefficient) := by gcongr
      _ = (20000 * q ^ 2 * delta) * coefficient := by ring
  have hcancel :
      prop41TangencyProductCoefficient * (tangency + q * delta) <=
        20000 * q ^ 2 * delta := by
    have hwithCoefficient :
        prop41TangencyProductCoefficient * (tangency + q * delta) *
            coefficient <=
          (20000 * q ^ 2 * delta) * coefficient := by
      calc
        prop41TangencyProductCoefficient * (tangency + q * delta) *
            coefficient <=
          20000 * (q * delta) * (q * t) := hproduct
        _ <= (20000 * q ^ 2 * delta) * coefficient := hright
    nlinarith
  have hcoefficientProduct :
      prop41TangencyProductCoefficient * tangency <=
        20000 * q ^ 2 * delta := by
    have hfixed := prop41TangencyProductCoefficient_pos
    nlinarith
  have hfactorIdentity :
      prop41TangencyScaleFactor q * delta =
        (20000 * q ^ 2 * delta) / prop41TangencyProductCoefficient := by
    rw [prop41TangencyScaleFactor]
    field_simp [ne_of_gt prop41TangencyProductCoefficient_pos]
  rw [hfactorIdentity]
  exact (le_div_iff₀ prop41TangencyProductCoefficient_pos).2 (by
    nlinarith)

/-- The final paper smallness condition for the produced scale factor is
strong enough for the analytic `q * delta < coefficient / 2400` branch. -/
theorem q_mul_delta_lt_coefficient_div_2400_of_scaleSmall
    {delta t coefficient q : Real}
    (hdelta : 0 < delta) (_ht : 0 < t)
    (hq : 1 <= q) (hcoefficient : t <= coefficient)
    (hsmall : prop41TangencyScaleFactor q * delta < t / 1200) :
    q * delta < coefficient / 2400 := by
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hfactorLower : 2 * q <= prop41TangencyScaleFactor q := by
    rw [prop41TangencyScaleFactor]
    apply (le_div_iff₀ prop41TangencyProductCoefficient_pos).2
    have hfixedLeOne : prop41TangencyProductCoefficient <= 1 := by
      norm_num [prop41TangencyProductCoefficient]
    have hqSquare : q <= q ^ 2 := by nlinarith
    have hleft :
        (2 * q) * prop41TangencyProductCoefficient <= 2 * q := by
      nlinarith [prop41TangencyProductCoefficient_pos]
    nlinarith
  have htwice : 2 * (q * delta) <=
      prop41TangencyScaleFactor q * delta := by
    nlinarith
  nlinarith

#print axioms prop41TangencyProductCoefficient_pos
#print axioms tangency_le_prop41TangencyScaleFactor_mul_delta_of_product
#print axioms q_mul_delta_lt_coefficient_div_2400_of_scaleSmall

end

end FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
