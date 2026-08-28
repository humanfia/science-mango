import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Odd-constant obstruction to a fourfold root ratio

For a monic integer polynomial with odd constant coefficient, the polynomial
and its root-scaled copy by four have nonzero resultant.  The proof reduces
the Sylvester determinant modulo two: four becomes zero, so the scaled copy
is a pure power of `X`, while the original constant coefficient becomes one.

This is an algebraic obstruction only.  Applying it to a lattice requires a
separate proof that the relevant reduced characteristic polynomial has
integer coefficients and odd constant coefficient.
-/

namespace ArchonPhysics.OddConstantScaleRootsResultant

open Polynomial

noncomputable section

/-- A monic integer polynomial with odd constant coefficient cannot share a
root with its fourfold root scaling, as witnessed by the nonzero fixed-size
resultant. -/
theorem int_resultant_scaleRoots_four_ne_zero_of_odd_constant
    (p : Polynomial Int) (hp : p.Monic) (hodd : Odd (p.coeff 0)) :
    Polynomial.resultant p (p.scaleRoots 4) p.natDegree p.natDegree ≠ 0 := by
  let phi : Int →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hlead : phi p.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff]
    norm_num
  have hconst : (p.map phi).coeff 0 = 1 := by
    rcases hodd with ⟨k, hk⟩
    rw [Polynomial.coeff_map, hk]
    rw [map_add, map_mul]
    have htwo : phi 2 = 0 := by
      change (2 : ZMod 2) = 0
      decide
    rw [htwo]
    simp
  have hdegree : (p.map phi).natDegree = p.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero phi hlead
  have hscale :
      (p.scaleRoots 4).map phi =
        (p.map phi).scaleRoots (phi 4) :=
    Polynomial.map_scaleRoots p 4 phi hlead
  have hmapped :
      phi (Polynomial.resultant p (p.scaleRoots 4)
        p.natDegree p.natDegree) = 1 := by
    rw [← Polynomial.resultant_map_map, hscale]
    have hfour : phi 4 = 0 := by
      change (4 : ZMod 2) = 0
      decide
    rw [hfour, Polynomial.scaleRoots_zero, (hp.map phi).leadingCoeff,
      one_smul, hdegree]
    rw [Polynomial.resultant_X_pow_right _ _ _ hdegree.le]
    simp [hconst]
  intro hzero
  rw [hzero, map_zero] at hmapped
  exact zero_ne_one hmapped

end

end ArchonPhysics.OddConstantScaleRootsResultant
