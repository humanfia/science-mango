import Mathlib

/-!
# PBB non-CSS commutation for code [[144,12,12]]

Perturbed bivariate-bicycle (non-CSS) code on the torus `ZMod 12 × ZMod 6`
with block-1 stabilizer polynomials
  A = x^1·y^2 + x^10·y^3 + x^10·y^4
  B = 1 + x^1·y^5 + x^11·y^4
  C = x^1·y^3 + x^10·y^3
  D = x^1·y^5 + x^10·y^5
over 𝔽₂.  Within-block-1 commutation of the X/Z stabilizers holds iff the
group-algebra element  `M = A·Cᵀ + B·Dᵀ`  is antipode-symmetric (`M = Mᵀ`),
i.e. `M` is closed under `g ↦ -g`.

Source: qcode-discovery campaign7_publication_merged, code_id `12_6_0193`.
-/

namespace Code_12_6_0193

abbrev G := ZMod 12 × ZMod 6

/-- Parity polynomial `A` (support, over 𝔽₂). -/
def A : List G := [(1, 2), (10, 3), (10, 4)]
/-- Parity polynomial `B`. -/
def B : List G := [(0, 0), (1, 5), (11, 4)]
/-- Perturbation polynomial `C` (z-part of block 1, left). -/
def C : List G := [(1, 3), (10, 3)]
/-- Perturbation polynomial `D` (z-part of block 1, right). -/
def D : List G := [(1, 5), (10, 5)]

/-- Toggle `g` in an 𝔽₂ support list (add mod 2). -/
def xorIns (p : List G) (g : G) : List G := if g ∈ p then p.erase g else g :: p

/-- Support of `P * Qᵀ` over 𝔽₂: XOR of all monomials `p - q` (antipode on `Q`). -/
def mulT (P Q : List G) : List G :=
  (P.flatMap (fun a => Q.map (fun c => a - c))).foldl xorIns []

/-- `M = A·Cᵀ + B·Dᵀ` (𝔽₂ addition = XOR of supports). -/
def M : List G := (mulT B D).foldl xorIns (mulT A C)

set_option maxRecDepth 100000 in
/-- **Within-block-1 commutation**: `M` is closed under the antipode `g ↦ -g`
    (equivalently `M = Mᵀ`), so the X/Z stabilizers of block 1 commute. -/
theorem pbb_commute : ∀ g ∈ M, (-g) ∈ M := by decide

end Code_12_6_0193
