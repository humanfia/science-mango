import Mathlib

/-!
# PBB non-CSS commutation for code [[180,6,18]]

Perturbed bivariate-bicycle (non-CSS) code on the torus `ZMod 15 × ZMod 6`
with block-1 stabilizer polynomials
  A = x^11·y^1 + x^9·y^1 + x^7·y^4
  B = 1 + x^5·y^1 + x^7·y^5
  C = x^7·y^4 + x^9·y^4
  D = x^9·y^5 + x^11·y^2
over 𝔽₂.  Within-block-1 commutation of the X/Z stabilizers holds iff the
group-algebra element  `M = A·Cᵀ + B·Dᵀ`  is antipode-symmetric (`M = Mᵀ`),
i.e. `M` is closed under `g ↦ -g`.

Source: qcode-discovery campaign7_publication_merged, code_id `Code_l15m6_52`.
-/

namespace Code_l15m6_52

abbrev G := ZMod 15 × ZMod 6

/-- Parity polynomial `A` (support, over 𝔽₂). -/
def A : List G := [(11, 1), (9, 1), (7, 4)]
/-- Parity polynomial `B`. -/
def B : List G := [(0, 0), (5, 1), (7, 5)]
/-- Perturbation polynomial `C` (z-part of block 1, left). -/
def C : List G := [(7, 4), (9, 4)]
/-- Perturbation polynomial `D` (z-part of block 1, right). -/
def D : List G := [(9, 5), (11, 2)]

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

end Code_l15m6_52
