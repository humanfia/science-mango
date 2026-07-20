import Mathlib

/-!
# CSS orthogonality for BB code [[288,32,<=10]]

Bivariate-bicycle code on the torus `ZMod 12 × ZMod 12` with parity-check
polynomials
  A = 1 + y^1 + y^8
  B = 1 + x^4 + x^8
over 𝔽₂.  CSS orthogonality  `H_X H_Zᵀ = A*B + B*A = 0`  in the group algebra.

Source: qcode-discovery ilp_catalog, label `[[288,32,<=10]]`.
-/

open AddMonoidAlgebra

namespace Code_288_32_10_l12m12_87

abbrev GA := AddMonoidAlgebra (ZMod 2) (ZMod 12 × ZMod 12)

/-- Monomial `x^a y^b` as a basis element of the group algebra. -/
noncomputable def mono (a : ZMod 12) (b : ZMod 12) : GA :=
  AddMonoidAlgebra.single (a, b) 1

/-- Characteristic 2 lifts from the coefficient ring `ZMod 2`. -/
instance : CharP GA 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) GA).injective 2

/-- Parity-check polynomial `A` of code `[[288,32,<=10]]`. -/
noncomputable def A : GA := mono 0 0 + mono 0 1 + mono 0 8

/-- Parity-check polynomial `B` of code `[[288,32,<=10]]`. -/
noncomputable def B : GA := mono 0 0 + mono 4 0 + mono 8 0

/-- **CSS orthogonality**: `H_X H_Zᵀ = A*B + B*A = 0` over 𝔽₂. -/
theorem css_orthogonal : A * B + B * A = 0 := by
  rw [mul_comm B A]
  exact CharTwo.add_self_eq_zero _

end Code_288_32_10_l12m12_87
