import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV7

noncomputable section

theorem one_eq_3456_cube_mul_coe_inverse_cube :
    (1 : ENNReal) = (3456 : ENNReal) ^ 3 *
      ((1 / 3456 : NNReal) : ENNReal) ^ 3 := by
  have hmul : (3456 : ENNReal) *
      (((3456 : NNReal) : ENNReal))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc
    (1 : ENNReal) = (1 : ENNReal) ^ 3 := by norm_num
    _ = ((3456 : ENNReal) *
        (((3456 : NNReal) : ENNReal))⁻¹) ^ 3 := by rw [hmul]
    _ = (3456 : ENNReal) ^ 3 *
        (((3456 : NNReal) : ENNReal))⁻¹ ^ 3 := mul_pow _ _ _
    _ = (3456 : ENNReal) ^ 3 *
        ((1 / 3456 : NNReal) : ENNReal) ^ 3 := by
      simp only [div_eq_mul_inv, one_mul]
      rw [ENNReal.coe_inv (by norm_num : (3456 : NNReal) ≠ 0)]

#print axioms one_eq_3456_cube_mul_coe_inverse_cube

end
end Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV7
