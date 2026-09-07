import Mathlib.Tactic

/-!
# Density budget through eighth normalization and finite selection

This pure `ENNReal` lemma isolates the factor `128` from honest eighth
normalization and an arbitrary finite selection loss.  It is the scalar
adapter from the exact-assembly neighborhood density lower bound to the
normalized Frostman density premise.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8EighthNormalizationSelectionDensityBudgetAlgebraV1

/-- If `source / 128 <= normalized`, then a source lower bound absorbing
`128 * loss` yields the normalized density budget after division by loss. -/
theorem target_le_normalized_div_loss_of_mul_128_loss_le_lower
    (target source normalized lower loss : ENNReal)
    (hloss0 : loss ≠ 0) (hlossTop : loss ≠ ∞)
    (hlower : lower <= source)
    (hnormalized : source / 128 <= normalized)
    (hbudget : target * (128 * loss) <= lower) :
    target <= normalized / loss := by
  have hsource : target * (128 * loss) <= source :=
    hbudget.trans hlower
  have hdiv : target <= source / 128 / loss := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hloss0) (Or.inl hlossTop)).2
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (128 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (128 : ENNReal) ≠ ∞))).2
    calc
      (target * loss) * 128 = target * (128 * loss) := by ac_rfl
      _ <= source := hsource
  exact hdiv.trans (ENNReal.div_le_div_right hnormalized loss)

#print axioms
  target_le_normalized_div_loss_of_mul_128_loss_le_lower

end Family8EighthNormalizationSelectionDensityBudgetAlgebraV1
