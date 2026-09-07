import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8AllSlabRowPowerAlgebraV1

noncomputable section

/-!
# All-slab row power cancellation

This file isolates the scalar cancellation behind the fixed-`theta` slab-row
sum.  It makes no geometric claim: all four scale/count parameters are
assumed positive and finite explicitly.
-/

/-- If `p = 1 - beta / 2` and `q = beta / 2`, the Jacobian row weight
exactly cancels the row Frostman and row-cardinality powers. -/
theorem allSlab_rowPower_identity
    (C G m w : ENNReal) (beta : Real)
    (hCTop : C ≠ ⊤) (hGTop : G ≠ ⊤)
    (hm0 : m ≠ 0) (hmTop : m ≠ ⊤)
    (hw0 : w ≠ 0) (hwTop : w ≠ ⊤)
    (hbeta0 : 0 <= beta) (hbetaTwo : beta <= 2) :
    w * (C * w * G / m) ^ (-(1 - beta / 2)) *
        (m / w) ^ (beta / 2) =
      C ^ (-(1 - beta / 2)) * G ^ (-(1 - beta / 2)) * m := by
  let p : Real := 1 - beta / 2
  let q : Real := beta / 2
  have hp : 0 <= p := by
    dsimp only [p]
    linarith
  have hq : 0 <= q := by
    dsimp only [q]
    linarith
  have hpq : p + q = 1 := by
    dsimp only [p, q]
    ring
  have hCwTop : C * w ≠ ⊤ := ENNReal.mul_ne_top hCTop hwTop
  have hCwGTop : C * w * G ≠ ⊤ :=
    ENNReal.mul_ne_top hCwTop hGTop
  have hmainPower :
      (C * w * G / m) ^ (-p) =
        C ^ (-p) * w ^ (-p) * G ^ (-p) * m ^ p := by
    rw [div_eq_mul_inv,
      ENNReal.mul_rpow_of_ne_top hCwGTop
        (ENNReal.inv_ne_top.mpr hm0),
      ENNReal.mul_rpow_of_ne_top hCwTop hGTop,
      ENNReal.mul_rpow_of_ne_top hCTop hwTop,
      ENNReal.inv_rpow, ENNReal.rpow_neg]
    rw [ENNReal.rpow_neg m p, inv_inv]
  have hratioPower :
      (m / w) ^ q = m ^ q * w ^ (-q) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ hq, div_eq_mul_inv,
      <- ENNReal.rpow_neg]
  have hwPower : w * w ^ (-p) * w ^ (-q) = 1 := by
    calc
      w * w ^ (-p) * w ^ (-q) =
          w ^ (1 : Real) * w ^ (-p) * w ^ (-q) := by
        rw [ENNReal.rpow_one]
      _ = w ^ (1 + (-p)) * w ^ (-q) := by
        rw [ENNReal.rpow_add 1 (-p) hw0 hwTop]
      _ = w ^ ((1 + (-p)) + (-q)) := by
        rw [ENNReal.rpow_add (1 + (-p)) (-q) hw0 hwTop]
      _ = 1 := by
        rw [show (1 + (-p)) + (-q) = 0 by linarith,
          ENNReal.rpow_zero]
  have hmPower : m ^ p * m ^ q = m := by
    calc
      m ^ p * m ^ q = m ^ (p + q) := by
        rw [ENNReal.rpow_add p q hm0 hmTop]
      _ = m := by rw [hpq, ENNReal.rpow_one]
  change
    w * (C * w * G / m) ^ (-p) * (m / w) ^ q =
      C ^ (-p) * G ^ (-p) * m
  rw [hmainPower, hratioPower]
  calc
    w * (C ^ (-p) * w ^ (-p) * G ^ (-p) * m ^ p) *
        (m ^ q * w ^ (-q)) =
      C ^ (-p) * G ^ (-p) *
        (w * w ^ (-p) * w ^ (-q)) * (m ^ p * m ^ q) := by
      ac_rfl
    _ = C ^ (-p) * G ^ (-p) * m := by rw [hwPower, hmPower, mul_one]

/-- The remaining global-mass factor after summing the row masses has the
expected positive exponent `beta / 2`. -/
theorem allSlab_globalMass_power_identity
    (G : ENNReal) (beta : Real) (hG0 : G ≠ 0) (hGTop : G ≠ ⊤) :
    G ^ (-(1 - beta / 2)) * G = G ^ (beta / 2) := by
  calc
    G ^ (-(1 - beta / 2)) * G =
        G ^ (-(1 - beta / 2)) * G ^ (1 : Real) := by
      rw [ENNReal.rpow_one]
    _ = G ^ (-(1 - beta / 2) + 1) := by
      rw [ENNReal.rpow_add (-(1 - beta / 2)) 1 hG0 hGTop]
    _ = G ^ (beta / 2) := by
      congr 1
      ring

/-- Common coefficients can be carried unchanged through the final
global-mass power cancellation. -/
theorem allSlab_commonCoefficient_globalMass_identity
    (C G k : ENNReal) (beta : Real) (hG0 : G ≠ 0) (hGTop : G ≠ ⊤) :
    k * C ^ (-(1 - beta / 2)) *
        G ^ (-(1 - beta / 2)) * G =
      k * C ^ (-(1 - beta / 2)) * G ^ (beta / 2) := by
  calc
    k * C ^ (-(1 - beta / 2)) *
        G ^ (-(1 - beta / 2)) * G =
      k * C ^ (-(1 - beta / 2)) *
        (G ^ (-(1 - beta / 2)) * G) := by ac_rfl
    _ = k * C ^ (-(1 - beta / 2)) * G ^ (beta / 2) := by
      rw [allSlab_globalMass_power_identity G beta hG0 hGTop]

/-- An upper bound for the row Frostman constant reverses after the
nonpositive Frostman power.  This is the direct normalized-row lower bound
used before multiplying by the Jacobian weight. -/
theorem allSlab_monotone_rowLower
    (C G m w rowCF k u : ENNReal) (beta : Real)
    (hbetaTwo : beta <= 2)
    (hrowCF : rowCF <= C * w * G / m)
    (hrow :
      k * rowCF ^ (-(1 - beta / 2)) * (m / w) ^ (beta / 2) <= u) :
    k * (C * w * G / m) ^ (-(1 - beta / 2)) *
        (m / w) ^ (beta / 2) <= u := by
  have hp : 0 <= 1 - beta / 2 := by linarith
  have hnegativePower :
      (C * w * G / m) ^ (-(1 - beta / 2)) <=
        rowCF ^ (-(1 - beta / 2)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
    exact ENNReal.rpow_le_rpow hrowCF hp
  calc
    k * (C * w * G / m) ^ (-(1 - beta / 2)) *
        (m / w) ^ (beta / 2) <=
      k * rowCF ^ (-(1 - beta / 2)) *
        (m / w) ^ (beta / 2) := by
      exact mul_le_mul' (mul_le_mul' le_rfl hnegativePower) le_rfl
    _ <= u := hrow

/-- Weighted form of `allSlab_monotone_rowLower`: after multiplying by the
row Jacobian weight, the dependence on both `w` and the row count `m / w`
cancels exactly. -/
theorem allSlab_weighted_rowLower
    (C G m w rowCF k u : ENNReal) (beta : Real)
    (hCTop : C ≠ ⊤) (hGTop : G ≠ ⊤)
    (hm0 : m ≠ 0) (hmTop : m ≠ ⊤)
    (hw0 : w ≠ 0) (hwTop : w ≠ ⊤)
    (hbeta0 : 0 <= beta) (hbetaTwo : beta <= 2)
    (hrowCF : rowCF <= C * w * G / m)
    (hrow :
      k * rowCF ^ (-(1 - beta / 2)) * (m / w) ^ (beta / 2) <= u) :
    k * (C ^ (-(1 - beta / 2)) *
      G ^ (-(1 - beta / 2)) * m) <= w * u := by
  have hnormalized := allSlab_monotone_rowLower
    C G m w rowCF k u beta hbetaTwo hrowCF hrow
  have hidentity := allSlab_rowPower_identity C G m w beta
    hCTop hGTop hm0 hmTop hw0 hwTop hbeta0 hbetaTwo
  calc
    k * (C ^ (-(1 - beta / 2)) *
        G ^ (-(1 - beta / 2)) * m) =
      w * (k * (C * w * G / m) ^ (-(1 - beta / 2)) *
        (m / w) ^ (beta / 2)) := by
      rw [<- hidentity]
      ac_rfl
    _ <= w * u := mul_le_mul' le_rfl hnormalized

#print axioms allSlab_rowPower_identity
#print axioms allSlab_globalMass_power_identity
#print axioms allSlab_commonCoefficient_globalMass_identity
#print axioms allSlab_monotone_rowLower
#print axioms allSlab_weighted_rowLower

end
end Family8AllSlabRowPowerAlgebraV1
