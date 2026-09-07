import Family8Grounding.Family8PolynomialJohnFrameBoxTestNetV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open scoped NNReal

namespace Family8PolynomialJohnFrameBoxCardPowerV1

open Family8PolynomialJohnFrameBoxTestNetV1

noncomputable section

/-!
# A directly consumable power bound for the John-frame-box catalogue

The exact catalogue count is a fifteenth power of an integer floor-window
length.  This file removes the floors.  Under the normalized scale range
`0 < delta <= 1/2`, every one-dimensional window has real cardinality at
most `46082 / delta`; hence the complete catalogue has cardinality at most
its fifteenth power.
-/

/-- A symmetric integer floor window around a nonnegative real number has
length at most `2 * x + 2`, after coercion to `Real`. -/
private theorem floorWindowLength_cast_le
    (x : Real) (hx : 0 <= x) :
    (((Int.floor x + 1 - Int.floor (-x)).toNat : Nat) : Real) <=
      2 * x + 2 := by
  have hfloorOrder : Int.floor (-x) <= Int.floor x := by
    apply Int.floor_le_floor
    linarith
  have hwindowNonneg :
      0 <= Int.floor x + 1 - Int.floor (-x) := by
    omega
  have htoNatCast :
      (((Int.floor x + 1 - Int.floor (-x)).toNat : Nat) : Real) =
        ((Int.floor x + 1 - Int.floor (-x) : Int) : Real) := by
    exact_mod_cast (Int.toNat_of_nonneg hwindowNonneg)
  rw [htoNatCast]
  have hfloorUpper : ((Int.floor x : Int) : Real) <= x :=
    Int.floor_le x
  have hnegativeFloorLower :
      -x < ((Int.floor (-x) : Int) : Real) + 1 :=
    Int.lt_floor_add_one (-x)
  push_cast
  linarith

/-- The literal floor-window factor in the catalogue count is bounded by
`46082 / delta`.  The harmless extra `2 / delta` absorbs the two endpoint
cells of the integer interval. -/
theorem floorWindowLength_cast_le_div
    (delta : NNReal) (hdelta : 0 < delta)
    (hdeltaUpper : delta <= (1 / 2 : NNReal)) :
    (((Int.floor (coordinateBound / parameterMesh delta) + 1 -
          Int.floor (-coordinateBound / parameterMesh delta)).toNat : Nat) :
        Real) <= 46082 / (delta : Real) := by
  have hmesh : 0 < parameterMesh delta := parameterMesh_pos hdelta
  have hx : 0 <= coordinateBound / parameterMesh delta := by
    apply div_nonneg
    · norm_num [coordinateBound]
    · exact hmesh.le
  have hbase := floorWindowLength_cast_le
    (coordinateBound / parameterMesh delta) hx
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.2 hdelta
  have hdeltaOneNN : delta <= (1 : NNReal) := by
    exact hdeltaUpper.trans (by norm_num)
  have hdeltaOne : (delta : Real) <= 1 := by
    exact_mod_cast hdeltaOneNN
  have hcoordinateRatio :
      coordinateBound / parameterMesh delta =
        23040 / (delta : Real) := by
    dsimp [coordinateBound, parameterMesh]
    field_simp
    ring
  have htwo : (2 : Real) <= 2 / (delta : Real) := by
    apply (le_div_iff₀ hdeltaReal).2
    nlinarith
  calc
    (((Int.floor (coordinateBound / parameterMesh delta) + 1 -
          Int.floor (-coordinateBound / parameterMesh delta)).toNat : Nat) :
        Real) <= 2 * (coordinateBound / parameterMesh delta) + 2 := by
          simpa [neg_div] using hbase
    _ = 46080 / (delta : Real) + 2 := by
      rw [hcoordinateRatio]
      ring
    _ <= 46080 / (delta : Real) + 2 / (delta : Real) := by
      gcongr
    _ = 46082 / (delta : Real) := by ring

/-- Floor-free polynomial cardinality bound, in the `Real` form consumed by
finite summation and logarithmic-tail arguments. -/
theorem card_catalogueIndex_real_le_div_pow
    (delta : NNReal) (hdelta : 0 < delta)
    (hdeltaUpper : delta <= (1 / 2 : NNReal)) :
    (Fintype.card (CatalogueIndex delta hdelta) : Real) <=
      (46082 / (delta : Real)) ^ 15 := by
  have hcard := card_catalogueIndex_le_floorPolynomial delta hdelta
  have hcardReal :
      (Fintype.card (CatalogueIndex delta hdelta) : Real) <=
        ((((Int.floor (coordinateBound / parameterMesh delta) + 1 -
            Int.floor (-coordinateBound / parameterMesh delta)).toNat : Nat) :
          Real) ^ 15) := by
    exact_mod_cast hcard
  calc
    (Fintype.card (CatalogueIndex delta hdelta) : Real) <=
        ((((Int.floor (coordinateBound / parameterMesh delta) + 1 -
            Int.floor (-coordinateBound / parameterMesh delta)).toNat : Nat) :
          Real) ^ 15) := hcardReal
    _ <= (46082 / (delta : Real)) ^ 15 := by
      gcongr
      exact floorWindowLength_cast_le_div delta hdelta hdeltaUpper

/-- Equivalent constant-times-inverse-power form, convenient when a later
tail estimate already factors all scale losses multiplicatively. -/
theorem card_catalogueIndex_real_le_constant_mul_inv_pow
    (delta : NNReal) (hdelta : 0 < delta)
    (hdeltaUpper : delta <= (1 / 2 : NNReal)) :
    (Fintype.card (CatalogueIndex delta hdelta) : Real) <=
      (46082 : Real) ^ 15 * ((delta : Real) ^ 15)⁻¹ := by
  have h := card_catalogueIndex_real_le_div_pow delta hdelta hdeltaUpper
  rw [div_pow] at h
  simpa [div_eq_mul_inv] using h

#print axioms floorWindowLength_cast_le_div
#print axioms card_catalogueIndex_real_le_div_pow
#print axioms card_catalogueIndex_real_le_constant_mul_inv_pow

end
end Family8PolynomialJohnFrameBoxCardPowerV1
