import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV7

open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4

noncomputable section

/-!
# Long-interval scale-power form of the exact conflict degree

The geometric scale connector only needs to bound the normalized squared
radius by `2 * globalDelta^(-2 epsilon)`.  Source Katz--Tao loss
`A <= globalDelta^(-eta)` then gives one incidence ratio power
`eta + 2 epsilon`; the exact degree squares it, hence the honest exponent
`2 eta + 4 epsilon`.
-/

/-- Arbitrary-scale version of the V4 power connector. -/
theorem exactConflictDegree_coe_le_of_ratio_bound
    {localDelta radius : NNReal} {A bound : ENNReal}
    (hratioOne :
      1 <= activeOwnerKatzTaoIncidenceRatio localDelta radius A)
    (hratioFinite :
      activeOwnerKatzTaoIncidenceRatio localDelta radius A ≠ ∞)
    (hratioBound :
      activeOwnerKatzTaoIncidenceRatio localDelta radius A <= bound) :
    ((1 +
        katzTaoDoubledFiberNatCap localDelta radius A *
          katzTaoDoubledParentsNatCap localDelta radius A : Nat) : ENNReal) <=
      8 * bound ^ 2 := by
  calc
    ((1 +
        katzTaoDoubledFiberNatCap localDelta radius A *
          katzTaoDoubledParentsNatCap localDelta radius A : Nat) : ENNReal) <=
        8 * (activeOwnerKatzTaoIncidenceRatio
          localDelta radius A) ^ 2 :=
      exactConflictDegree_coe_le_eight_mul_ratio_sq
        hratioOne hratioFinite
    _ <= 8 * bound ^ 2 := by gcongr

/-- A normalized radius bound and a source Katz--Tao power bound give the
literal incidence-ratio power estimate, with only the fixed coefficient
`480000`. -/
theorem activeOwnerKatzTaoIncidenceRatio_le_longIntervalPower
    {globalDelta localDelta radius : NNReal} {A : ENNReal}
    {epsilon eta : Real}
    (hglobal : 0 < globalDelta)
    (hA : A <= (globalDelta : ENNReal) ^ (-eta))
    (hscale :
      (radius : ENNReal) ^ 2 /
          ((localDelta : ENNReal) ^ 2 / 2) <=
        2 * (globalDelta : ENNReal) ^ (-2 * epsilon)) :
    activeOwnerKatzTaoIncidenceRatio localDelta radius A <=
      480000 * (globalDelta : ENNReal) ^ (-(eta + 2 * epsilon)) := by
  let d : ENNReal := (globalDelta : ENNReal)
  let scaleRatio : ENNReal :=
    (radius : ENNReal) ^ 2 / ((localDelta : ENNReal) ^ 2 / 2)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hglobal.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hfactor :
      activeOwnerKatzTaoIncidenceRatio localDelta radius A =
        240000 * A * scaleRatio := by
    unfold activeOwnerKatzTaoIncidenceRatio
    dsimp only [scaleRatio]
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hfactor]
  calc
    240000 * A * scaleRatio <=
        240000 * d ^ (-eta) *
          (2 * d ^ (-2 * epsilon)) := by
      exact mul_le_mul' (mul_le_mul' le_rfl hA)
        (by simpa only [d, scaleRatio] using hscale)
    _ = 480000 * (d ^ (-eta) * d ^ (-2 * epsilon)) := by ring
    _ = 480000 * d ^ ((-eta) + (-2 * epsilon)) := by
      rw [ENNReal.rpow_add (-eta) (-2 * epsilon) hd0 hdTop]
    _ = 480000 * d ^ (-(eta + 2 * epsilon)) := by
      congr 2
      ring

/-- The exact natural degree after both ceilings has the small power
`2 eta + 4 epsilon`, before absorbing its one fixed coefficient. -/
theorem exactConflictDegree_coe_le_longIntervalPower
    {globalDelta localDelta radius : NNReal} {A : ENNReal}
    {epsilon eta : Real}
    (hglobal : 0 < globalDelta)
    (hratioOne :
      1 <= activeOwnerKatzTaoIncidenceRatio localDelta radius A)
    (hratioFinite :
      activeOwnerKatzTaoIncidenceRatio localDelta radius A ≠ ∞)
    (hA : A <= (globalDelta : ENNReal) ^ (-eta))
    (hscale :
      (radius : ENNReal) ^ 2 /
          ((localDelta : ENNReal) ^ 2 / 2) <=
        2 * (globalDelta : ENNReal) ^ (-2 * epsilon)) :
    ((1 +
        katzTaoDoubledFiberNatCap localDelta radius A *
          katzTaoDoubledParentsNatCap localDelta radius A : Nat) : ENNReal) <=
      8 *
        (480000 *
          (globalDelta : ENNReal) ^ (-(eta + 2 * epsilon))) ^ 2 := by
  apply exactConflictDegree_coe_le_of_ratio_bound
    hratioOne hratioFinite
  exact activeOwnerKatzTaoIncidenceRatio_le_longIntervalPower
    hglobal hA hscale

#print axioms exactConflictDegree_coe_le_of_ratio_bound
#print axioms activeOwnerKatzTaoIncidenceRatio_le_longIntervalPower
#print axioms exactConflictDegree_coe_le_longIntervalPower

end
end Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV7
