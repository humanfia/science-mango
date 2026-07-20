import Mathlib

/-!
# CSS orthogonality for BB code [[360,24,<=8]]

Bivariate-bicycle code on the torus `ZMod 15 × ZMod 12` with parity-check
polynomials
  A = 1 + y^2 + y^4
  B = y^2 + x^6 + x^7
over 𝔽₂.  CSS orthogonality  `H_X H_Zᵀ = A*B + B*A = 0`  in the group algebra.

Source: qcode-discovery ilp_catalog, label `[[360,24,<=8]]`.
-/

open AddMonoidAlgebra

namespace Code_360_24_8_l15m12_124

abbrev GA := AddMonoidAlgebra (ZMod 2) (ZMod 15 × ZMod 12)

/-- Monomial `x^a y^b` as a basis element of the group algebra. -/
noncomputable def mono (a : ZMod 15) (b : ZMod 12) : GA :=
  AddMonoidAlgebra.single (a, b) 1

/-- Characteristic 2 lifts from the coefficient ring `ZMod 2`. -/
instance : CharP GA 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) GA).injective 2

/-- Parity-check polynomial `A` of code `[[360,24,<=8]]`. -/
noncomputable def A : GA := mono 0 0 + mono 0 2 + mono 0 4

/-- Parity-check polynomial `B` of code `[[360,24,<=8]]`. -/
noncomputable def B : GA := mono 0 2 + mono 6 0 + mono 7 0

/-- **CSS orthogonality**: `H_X H_Zᵀ = A*B + B*A = 0` over 𝔽₂. -/
theorem css_orthogonal : A * B + B * A = 0 := by
  rw [mul_comm B A]
  exact CharTwo.add_self_eq_zero _

end Code_360_24_8_l15m12_124
