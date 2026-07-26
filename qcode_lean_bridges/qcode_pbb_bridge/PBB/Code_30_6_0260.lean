import Mathlib

/-!
# PBB non-CSS commutation for code [[360,12,20]]

Perturbed bivariate-bicycle (non-CSS) code on the torus `ZMod 30 × ZMod 6`
with block-1 stabilizer polynomials
  A = x^13·y^4 + x^22·y^3 + x^22·y^2
  B = 1 + x^13·y^1 + x^5·y^2
  C = x^13·y^3 + x^22·y^3
  D = x^13·y^1 + x^22·y^1
over 𝔽₂.  Within-block-1 commutation of the X/Z stabilizers holds iff the
group-algebra element  `M = A·Cᵀ + B·Dᵀ`  is antipode-symmetric (`M = Mᵀ`),
i.e. `M` is closed under `g ↦ -g`.

Source: qcode-discovery campaign7_publication_merged, code_id `30_6_0260`.
-/

namespace Code_30_6_0260

abbrev G := ZMod 30 × ZMod 6

/-- Parity polynomial `A` (support, over 𝔽₂). -/
def A : List G := [(13, 4), (22, 3), (22, 2)]
/-- Parity polynomial `B`. -/
def B : List G := [(0, 0), (13, 1), (5, 2)]
/-- Perturbation polynomial `C` (z-part of block 1, left). -/
def C : List G := [(13, 3), (22, 3)]
/-- Perturbation polynomial `D` (z-part of block 1, right). -/
def D : List G := [(13, 1), (22, 1)]

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

end Code_30_6_0260
