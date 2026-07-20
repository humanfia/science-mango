import Mathlib

/-!
# PBB non-CSS commutation for code [[180,8,14]]

Perturbed bivariate-bicycle (non-CSS) code on the torus `ZMod 15 × ZMod 6`
with block-1 stabilizer polynomials
  A = x^14·y^2 + x^11·y^3 + x^11·y^4
  B = 1 + x^14·y^5 + x^10·y^4
  C = x^11·y^1 + x^14·y^5
  D = x^11·y^3 + x^14·y^1
over 𝔽₂.  Within-block-1 commutation of the X/Z stabilizers holds iff the
group-algebra element  `M = A·Cᵀ + B·Dᵀ`  is antipode-symmetric (`M = Mᵀ`),
i.e. `M` is closed under `g ↦ -g`.

Source: qcode-discovery campaign7_publication_merged, code_id `Code_l15m6_90`.
-/

namespace Code_l15m6_90

abbrev G := ZMod 15 × ZMod 6

/-- Parity polynomial `A` (support, over 𝔽₂). -/
def A : List G := [(14, 2), (11, 3), (11, 4)]
/-- Parity polynomial `B`. -/
def B : List G := [(0, 0), (14, 5), (10, 4)]
/-- Perturbation polynomial `C` (z-part of block 1, left). -/
def C : List G := [(11, 1), (14, 5)]
/-- Perturbation polynomial `D` (z-part of block 1, right). -/
def D : List G := [(11, 3), (14, 1)]

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

end Code_l15m6_90
