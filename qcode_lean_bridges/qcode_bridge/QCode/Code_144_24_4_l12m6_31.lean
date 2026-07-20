import Mathlib

/-!
# CSS orthogonality for BB code [[144,24,<=4]]

Bivariate-bicycle code on the torus `ZMod 12 × ZMod 6` with parity-check
polynomials
  A = y^2 + x^1 + x^2·y^1
  B = y^2 + x^1 + x^2·y^1
over 𝔽₂.  CSS orthogonality  `H_X H_Zᵀ = A*B + B*A = 0`  in the group algebra.

Source: qcode-discovery ilp_catalog, label `[[144,24,<=4]]`.
-/

open AddMonoidAlgebra

namespace Code_144_24_4_l12m6_31

abbrev GA := AddMonoidAlgebra (ZMod 2) (ZMod 12 × ZMod 6)

/-- Monomial `x^a y^b` as a basis element of the group algebra. -/
noncomputable def mono (a : ZMod 12) (b : ZMod 6) : GA :=
  AddMonoidAlgebra.single (a, b) 1

/-- Characteristic 2 lifts from the coefficient ring `ZMod 2`. -/
instance : CharP GA 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) GA).injective 2

/-- Parity-check polynomial `A` of code `[[144,24,<=4]]`. -/
noncomputable def A : GA := mono 0 2 + mono 1 0 + mono 2 1

/-- Parity-check polynomial `B` of code `[[144,24,<=4]]`. -/
noncomputable def B : GA := mono 0 2 + mono 1 0 + mono 2 1

/-- **CSS orthogonality**: `H_X H_Zᵀ = A*B + B*A = 0` over 𝔽₂. -/
theorem css_orthogonal : A * B + B * A = 0 := by
  rw [mul_comm B A]
  exact CharTwo.add_self_eq_zero _

end Code_144_24_4_l12m6_31
