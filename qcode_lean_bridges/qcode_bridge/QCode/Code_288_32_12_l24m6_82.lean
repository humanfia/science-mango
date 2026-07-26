import Mathlib

/-!
# CSS orthogonality for BB code [[288,32,<=12]]

Bivariate-bicycle code on the torus `ZMod 24 × ZMod 6` with parity-check
polynomials
  A = 1 + y^2 + y^4
  B = 1 + x^20 + x^22
over 𝔽₂.  CSS orthogonality  `H_X H_Zᵀ = A*B + B*A = 0`  in the group algebra.

Source: qcode-discovery ilp_catalog, label `[[288,32,<=12]]`.
-/

open AddMonoidAlgebra

namespace Code_288_32_12_l24m6_82

abbrev GA := AddMonoidAlgebra (ZMod 2) (ZMod 24 × ZMod 6)

/-- Monomial `x^a y^b` as a basis element of the group algebra. -/
noncomputable def mono (a : ZMod 24) (b : ZMod 6) : GA :=
  AddMonoidAlgebra.single (a, b) 1

/-- Characteristic 2 lifts from the coefficient ring `ZMod 2`. -/
instance : CharP GA 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) GA).injective 2

/-- Parity-check polynomial `A` of code `[[288,32,<=12]]`. -/
noncomputable def A : GA := mono 0 0 + mono 0 2 + mono 0 4

/-- Parity-check polynomial `B` of code `[[288,32,<=12]]`. -/
noncomputable def B : GA := mono 0 0 + mono 20 0 + mono 22 0

/-- **CSS orthogonality**: `H_X H_Zᵀ = A*B + B*A = 0` over 𝔽₂. -/
theorem css_orthogonal : A * B + B * A = 0 := by
  rw [mul_comm B A]
  exact CharTwo.add_self_eq_zero _

end Code_288_32_12_l24m6_82
