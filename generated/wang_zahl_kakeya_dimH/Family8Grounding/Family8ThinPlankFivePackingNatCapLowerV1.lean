import Family8Grounding.Family8ThinPlankFiveParameterPackingV2
import Mathlib.Tactic

/-!
# Lower envelope for the five-parameter thin-plank packing cap

The two wide grid coordinates give at least the square of the requested
aspect ratio.  This is the lower-bound counterpart of the packing theorem's
usual cardinality upper bound and uses the literal floor-grid definition.
-/

open scoped ENNReal NNReal

namespace Family8ThinPlankFivePackingNatCapLowerV1

open Family8ThinPlankEssentialDistinctPackingV4
open Family8ThinPlankFiveParameterPackingV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- A symmetric integer floor window around a nonnegative real has length at
least its positive radius. -/
private theorem le_floorWindowLength_cast (x : Real) (hx : 0 <= x) :
    x <= (((Int.floor x + 1 - Int.floor (-x)).toNat : Nat) : Real) := by
  have hfloorNonneg : 0 <= Int.floor x := Int.floor_nonneg.mpr hx
  have hwindowNonneg :
      0 <= Int.floor x + 1 - Int.floor (-x) := by
    have hnegativeFloor : Int.floor (-x) <= 0 := by
      have h := Int.floor_le_floor (show -x <= (0 : Real) by linarith)
      simpa using h
    omega
  have htoNatCast :
      (((Int.floor x + 1 - Int.floor (-x)).toNat : Nat) : Real) =
        ((Int.floor x + 1 - Int.floor (-x) : Int) : Real) := by
    exact_mod_cast (Int.toNat_of_nonneg hwindowNonneg)
  rw [htoNatCast]
  have hnegativeFloorUpper :
      ((Int.floor (-x) : Int) : Real) <= -x := Int.floor_le (-x)
  have hfloorNonnegReal : (0 : Real) <= (Int.floor x : Int) := by
    exact_mod_cast hfloorNonneg
  push_cast
  linarith

/-- The literal two-wide-coordinate code count dominates `R^2` for every
nonnegative real aspect `R`. -/
theorem sq_le_thinPlankWideCodeCount_cast (R : Real) (hR : 0 <= R) :
    R ^ 2 <= (thinPlankWideCodeCount R : Real) := by
  have hmesh : (0 : Real) < thinPlankPackingMesh := by
    norm_num [thinPlankPackingMesh]
  have hRmesh : R <= R / thinPlankPackingMesh := by
    rw [thinPlankPackingMesh]
    norm_num
    nlinarith
  have hwindow := le_floorWindowLength_cast
    (R / thinPlankPackingMesh) (div_nonneg hR hmesh.le)
  have hbase :
      R <= (((Int.floor (R / thinPlankPackingMesh) + 1 -
        Int.floor (-R / thinPlankPackingMesh)).toNat : Nat) : Real) :=
    hRmesh.trans (by simpa [neg_div] using hwindow)
  unfold thinPlankWideCodeCount
  simpa only [Nat.cast_pow] using pow_le_pow_left₀ hR hbase 2

/-- The complete five-parameter natural cap still dominates `R^2`; its
fixed-coordinate factor is a positive natural number. -/
theorem sq_le_thinPlankFivePackingNatCap_cast (R : Real) (hR : 0 <= R) :
    R ^ 2 <= (thinPlankFivePackingNatCap R : Real) := by
  have hwide := sq_le_thinPlankWideCodeCount_cast R hR
  have hfixed : 1 <= thinPlankFiveFixedCodeCount := by
    unfold thinPlankFiveFixedCodeCount
    norm_num [thinPlankPackingFixedBound, thinPlankPackingMesh]
    rw [show (20000001 : Int).toNat = 20000001 by
      exact_mod_cast (Int.toNat_of_nonneg (by norm_num : (0 : Int) <= 20000001))]
    norm_num
  have hfixedReal : (1 : Real) <= thinPlankFiveFixedCodeCount := by
    exact_mod_cast hfixed
  unfold thinPlankFivePackingNatCap
  calc
    R ^ 2 <= (thinPlankWideCodeCount R : Real) := hwide
    _ <= (thinPlankFiveFixedCodeCount : Real) *
        (thinPlankWideCodeCount R : Real) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfixedReal
        (show (0 : Real) <= thinPlankWideCodeCount R by positivity)
    _ = ((thinPlankFiveFixedCodeCount * thinPlankWideCodeCount R : Nat) :
        Real) := by norm_num

/-- `ENNReal` form used directly by the Proposition 6.6(A) inner factor. -/
theorem aspect_sq_le_thinPlankFivePackingNatCap
    (a b : NNReal) (ha : 0 < a) :
    ((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat) <=
      (thinPlankFivePackingNatCap ((b : Real) / (a : Real)) : Nat) := by
  have haReal : (0 : Real) < (a : Real) := by exact_mod_cast ha
  have hbReal : (0 : Real) <= (b : Real) := NNReal.zero_le_coe
  have hreal := sq_le_thinPlankFivePackingNatCap_cast
    ((b : Real) / (a : Real)) (div_nonneg hbReal haReal.le)
  have hreal' :
      (((b / a : NNReal) : Real) ^ 2) <=
        (thinPlankFivePackingNatCap (((b / a : NNReal) : Real)) : Real) := by
    simpa only [NNReal.coe_div] using hreal
  have henn :
      (((b / a : NNReal) : ENNReal) ^ (2 : Nat)) <=
        (thinPlankFivePackingNatCap (((b / a : NNReal) : Real)) : Nat) := by
    exact_mod_cast hreal'
  simpa only [ENNReal.coe_div ha.ne', NNReal.coe_div] using henn

#print axioms sq_le_thinPlankWideCodeCount_cast
#print axioms sq_le_thinPlankFivePackingNatCap_cast
#print axioms aspect_sq_le_thinPlankFivePackingNatCap

end
end Family8ThinPlankFivePackingNatCapLowerV1
