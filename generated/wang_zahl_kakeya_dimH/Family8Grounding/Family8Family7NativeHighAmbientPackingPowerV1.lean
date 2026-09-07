import Family8Grounding.Family8Family7NativeHighAmbientPackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighAmbientPackingPowerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8Family7NativeHighAmbientPackingV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# A floor-free power bound for the genuine ambient packing cap

The midpoint grid has three coordinates and mesh `delta / 1000`, while the
direction packing has two effective coordinates.  Thus the explicit cap
from `Family8Family7NativeHighAmbientPackingV1` is at most a fixed constant
times `delta ^ (-5)`.  The final theorem applies this only to the genuine
upstream epsilon-extremal record, which retains unit-ball containment and
essential distinctness.
-/

/-- A symmetric integer floor window about a nonnegative real has length at
most `2 * x + 2` after coercion to `Real`. -/
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

/-- One midpoint coordinate contributes at most `2002 / delta` cells. -/
theorem nativeHighAmbientPositionWindow_cast_le_div
    (delta : NNReal) (hdeltaPos : 0 < delta)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    (((Int.floor
          (nativeHighAmbientPositionBound /
            nativeHighAmbientPositionMesh delta) + 1 -
        Int.floor
          (-nativeHighAmbientPositionBound /
            nativeHighAmbientPositionMesh delta)).toNat : Nat) : Real) <=
      2002 / (delta : Real) := by
  have hmesh : 0 < nativeHighAmbientPositionMesh delta := by
    exact div_pos (NNReal.coe_pos.mpr hdeltaPos) (by norm_num)
  have hx : 0 <=
      nativeHighAmbientPositionBound /
        nativeHighAmbientPositionMesh delta := by
    apply div_nonneg
    · norm_num [nativeHighAmbientPositionBound]
    · exact hmesh.le
  have hbase := floorWindowLength_cast_le
    (nativeHighAmbientPositionBound /
      nativeHighAmbientPositionMesh delta) hx
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have hdeltaOneNN : delta <= (1 : NNReal) :=
    hdeltaSmall.trans (by
      exact_mod_cast (show (1 : Real) / 100 <= 1 by norm_num))
  have hdeltaOne : (delta : Real) <= 1 := by
    exact_mod_cast hdeltaOneNN
  have hcoordinateRatio :
      nativeHighAmbientPositionBound /
          nativeHighAmbientPositionMesh delta =
        1000 / (delta : Real) := by
    dsimp [nativeHighAmbientPositionBound, nativeHighAmbientPositionMesh]
    field_simp
  have htwo : (2 : Real) <= 2 / (delta : Real) := by
    apply (le_div_iff₀ hdeltaReal).2
    nlinarith
  calc
    (((Int.floor
          (nativeHighAmbientPositionBound /
            nativeHighAmbientPositionMesh delta) + 1 -
        Int.floor
          (-nativeHighAmbientPositionBound /
            nativeHighAmbientPositionMesh delta)).toNat : Nat) : Real) <=
        2 * (nativeHighAmbientPositionBound /
          nativeHighAmbientPositionMesh delta) + 2 := by
      simpa [neg_div] using hbase
    _ = 2000 / (delta : Real) + 2 := by
      rw [hcoordinateRatio]
      ring
    _ <= 2000 / (delta : Real) + 2 / (delta : Real) := by
      gcongr
    _ = 2002 / (delta : Real) := by ring

/-- The three-dimensional midpoint code contributes `delta ^ (-3)`. -/
theorem nativeHighAmbientPositionCodeCap_real_le_rpow
    (delta : NNReal) (hdeltaPos : 0 < delta)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    (nativeHighAmbientPositionCodeCap delta : Real) <=
      (2002 : Real) ^ 3 * (delta : Real) ^ (-3 : Real) := by
  have hwindow := nativeHighAmbientPositionWindow_cast_le_div
    delta hdeltaPos hdeltaSmall
  have hcode :
      (nativeHighAmbientPositionCodeCap delta : Real) <=
        (2002 / (delta : Real)) ^ 3 := by
    unfold nativeHighAmbientPositionCodeCap
    simp only [Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hwindow 3
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have hrpow :
      (delta : Real) ^ (-3 : Real) = ((delta : Real) ^ 3)⁻¹ := by
    rw [show (-3 : Real) = ((-3 : Int) : Real) by norm_num,
      Real.rpow_intCast]
    norm_num [zpow_neg]
  calc
    (nativeHighAmbientPositionCodeCap delta : Real) <=
        (2002 / (delta : Real)) ^ 3 := hcode
    _ = (2002 : Real) ^ 3 * (delta : Real) ^ (-3 : Real) := by
      rw [div_pow, hrpow]
      ring

/-- Explicit coefficient in the global five-parameter packing bound. -/
def nativeHighAmbientPackingConstant : ENNReal :=
  ((2002 ^ 3 * 330000 : Nat) : ENNReal)

/-- The complete natural packing cap has the expected five-parameter power
bound. -/
theorem nativeHighAmbientPackingNatCap_coe_le_rpow
    (delta : NNReal) (hdeltaPos : 0 < delta)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    (nativeHighAmbientPackingNatCap delta : ENNReal) <=
      nativeHighAmbientPackingConstant *
        (delta : ENNReal) ^ (-5 : Real) := by
  have hpos := nativeHighAmbientPositionCodeCap_real_le_rpow
    delta hdeltaPos hdeltaSmall
  have hscalePos : 0 < delta / 100 := div_pos hdeltaPos (by norm_num)
  have hscaleOne : delta / 100 <= (1 : NNReal) := by
    apply (div_le_one (by norm_num : (0 : NNReal) < 100)).2
    exact hdeltaSmall.trans (by
      exact_mod_cast (show (1 : Real) / 100 <= 100 by norm_num))
  have hdirReal :=
    Family8SphereDirectionPackingENNRealV1.directionPackingNatCap_real_le_rpow
      (delta / 100) hscalePos hscaleOne
  have hdirReal2 :
      (commonPointDirectionCap delta : Real) <=
        33 * (((delta / 100 : NNReal) : Real) ^ (-2 : Real)) := by
    simpa only [commonPointDirectionCap,
      Family8SphereDirectionPackingENNRealV1.directionPackingNatCap] using
      hdirReal
  have hdirScaled :
      (commonPointDirectionCap delta : Real) <=
        330000 * (delta : Real) ^ (-2 : Real) := by
    calc
      (commonPointDirectionCap delta : Real) <=
          33 * (((delta / 100 : NNReal) : Real) ^ (-2 : Real)) := hdirReal2
      _ = 330000 * (delta : Real) ^ (-2 : Real) := by
        rw [coe_div_hundred_rpow_neg_two delta hdeltaPos]
        ring
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have hreal :
      (nativeHighAmbientPackingNatCap delta : Real) <=
        ((2002 ^ 3 * 330000 : Nat) : Real) *
          (delta : Real) ^ (-5 : Real) := by
    calc
      (nativeHighAmbientPackingNatCap delta : Real) =
          (nativeHighAmbientPositionCodeCap delta : Real) *
            (commonPointDirectionCap delta : Real) := by
        simp only [nativeHighAmbientPackingNatCap, Nat.cast_mul]
      _ <= ((2002 : Real) ^ 3 * (delta : Real) ^ (-3 : Real)) *
          (330000 * (delta : Real) ^ (-2 : Real)) := by
        exact mul_le_mul hpos hdirScaled (by positivity) (by positivity)
      _ = ((2002 ^ 3 * 330000 : Nat) : Real) *
          ((delta : Real) ^ (-3 : Real) *
            (delta : Real) ^ (-2 : Real)) := by
        push_cast
        ring
      _ = ((2002 ^ 3 * 330000 : Nat) : Real) *
          (delta : Real) ^ (-5 : Real) := by
        rw [← Real.rpow_add hdeltaReal]
        norm_num
  have hnn :
      (nativeHighAmbientPackingNatCap delta : NNReal) <=
        (2002 ^ 3 * 330000 : Nat) * delta ^ (-5 : Real) := by
    rw [← NNReal.coe_le_coe]
    simpa only [NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_rpow] using hreal
  rw [nativeHighAmbientPackingConstant,
    ← ENNReal.coe_rpow_of_ne_zero hdeltaPos.ne' (-5 : Real)]
  exact_mod_cast hnn

/-- The genuine extremal ambient family, unlike an arbitrary
`NativeBranchCore`, inherits the uniform `delta ^ (-5)` cap. -/
theorem extremalAmbient_card_coe_le_nativeHighAmbientPacking_rpow
    {delta : NNReal} {index : Type u} [Fintype index] [DecidableEq index]
    (S : WZL3UniformTubeSource delta index) (ambient : Finset index)
    {Y : Shading S.family.bodyFamily} {parallelLoss : Nat}
    {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      epsilon sigma)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    (ambient.card : ENNReal) <=
      nativeHighAmbientPackingConstant *
        (delta : ENNReal) ^ (-5 : Real) := by
  have hcard :
      (ambient.card : ENNReal) <=
        (nativeHighAmbientPackingNatCap delta : ENNReal) := by
    exact_mod_cast
      extremalAmbient_card_le_nativeHighAmbientPackingNatCap
        S ambient G hdeltaSmall
  exact hcard.trans
    (nativeHighAmbientPackingNatCap_coe_le_rpow
      delta G.delta_pos hdeltaSmall)

#print axioms nativeHighAmbientPositionWindow_cast_le_div
#print axioms nativeHighAmbientPositionCodeCap_real_le_rpow
#print axioms nativeHighAmbientPackingConstant
#print axioms nativeHighAmbientPackingNatCap_coe_le_rpow
#print axioms extremalAmbient_card_coe_le_nativeHighAmbientPacking_rpow

end
end Family8Family7NativeHighAmbientPackingPowerV1
