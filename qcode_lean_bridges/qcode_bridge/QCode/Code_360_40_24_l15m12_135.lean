import Mathlib

/-!
# CSS orthogonality for BB code [[360,40,<=24]]

Bivariate-bicycle code on the torus `ZMod 15 × ZMod 12` with parity-check
polynomials
  A = 1 + y^10 + y^11
  B = 1 + x^5 + x^10
over 𝔽₂.  CSS orthogonality  `H_X H_Zᵀ = A*B + B*A = 0`  in the group algebra.

Source: qcode-discovery ilp_catalog, label `[[360,40,<=24]]`.
-/

open AddMonoidAlgebra

namespace Code_360_40_24_l15m12_135

abbrev GA := AddMonoidAlgebra (ZMod 2) (ZMod 15 × ZMod 12)

/-- Monomial `x^a y^b` as a basis element of the group algebra. -/
noncomputable def mono (a : ZMod 15) (b : ZMod 12) : GA :=
  AddMonoidAlgebra.single (a, b) 1

/-- Characteristic 2 lifts from the coefficient ring `ZMod 2`. -/
instance : CharP GA 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) GA).injective 2

/-- Parity-check polynomial `A` of code `[[360,40,<=24]]`. -/
noncomputable def A : GA := mono 0 0 + mono 0 10 + mono 0 11

/-- Parity-check polynomial `B` of code `[[360,40,<=24]]`. -/
noncomputable def B : GA := mono 0 0 + mono 5 0 + mono 10 0

/-- **CSS orthogonality**: `H_X H_Zᵀ = A*B + B*A = 0` over 𝔽₂. -/
theorem css_orthogonal : A * B + B * A = 0 := by
  rw [mul_comm B A]
  exact CharTwo.add_self_eq_zero _

end Code_360_40_24_l15m12_135
