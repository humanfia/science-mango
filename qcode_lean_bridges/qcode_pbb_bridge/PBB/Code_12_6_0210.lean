import Mathlib

/-!
# PBB non-CSS commutation for code [[144,4,12]]

Perturbed bivariate-bicycle (non-CSS) code on the torus `ZMod 12 × ZMod 6`
with block-1 stabilizer polynomials
  A = x^6·y^4 + x^7·y^2 + x^3
  B = x^9·y^2 + x^3·y^4 + x^7·y^3
  C = x^5·y^1
  D = x^6
over 𝔽₂.  Within-block-1 commutation of the X/Z stabilizers holds iff the
group-algebra element  `M = A·Cᵀ + B·Dᵀ`  is antipode-symmetric (`M = Mᵀ`),
i.e. `M` is closed under `g ↦ -g`.

Source: qcode-discovery campaign7_publication_merged, code_id `12_6_0210`.
-/

namespace Code_12_6_0210

abbrev G := ZMod 12 × ZMod 6

/-- Parity polynomial `A` (support, over 𝔽₂). -/
def A : List G := [(6, 4), (7, 2), (3, 0)]
/-- Parity polynomial `B`. -/
def B : List G := [(9, 2), (3, 4), (7, 3)]
/-- Perturbation polynomial `C` (z-part of block 1, left). -/
def C : List G := [(5, 1)]
/-- Perturbation polynomial `D` (z-part of block 1, right). -/
def D : List G := [(6, 0)]

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

end Code_12_6_0210
