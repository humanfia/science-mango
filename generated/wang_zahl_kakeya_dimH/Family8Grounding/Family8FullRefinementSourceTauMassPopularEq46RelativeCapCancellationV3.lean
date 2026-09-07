import Family8Grounding.Family8LocalFiberCapRelativeSquareCancellationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open scoped ENNReal NNReal

namespace Family8FullRefinementSourceTauMassPopularEq46RelativeCapCancellationV3

open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8LocalFiberCapRelativeSquareCancellationV1

noncomputable section

/-!
# Sharp source-cap cancellation at the actual relative scale

V1 and V2 were unbuilt syntax/orientation drafts and are intentionally not
imported.  This numerical core is independent of the large dependent
selected-parent datum: its `rhs` may retain the literal actual
`tubesPerPlank` count, while only the source Katz--Tao cap is cancelled.
-/

/-- Abstract division-free cancellation of a positive finite relative-scale
factor. -/
theorem sourceCap_le_of_relativeSquare
    (sourceCap : Nat) {relativeSquare capBound core rhs : ENNReal}
    (hrelative0 : relativeSquare ≠ 0)
    (hrelativeTop : relativeSquare ≠ ∞)
    (hcap : (sourceCap : ENNReal) * relativeSquare ≤ capBound)
    (hscaled : capBound * core ≤ relativeSquare * rhs) :
    (sourceCap : ENNReal) * core ≤ rhs := by
  apply (ENNReal.mul_le_mul_iff_right hrelative0 hrelativeTop).mp
  calc
    relativeSquare * ((sourceCap : ENNReal) * core) =
        ((sourceCap : ENNReal) * relativeSquare) * core := by ac_rfl
    _ ≤ capBound * core := mul_le_mul' hcap le_rfl
    _ ≤ relativeSquare * rhs := hscaled

/-- The canonical source Katz--Tao cap disappears after multiplication by
the exact `(delta / tau)^2` factor.  No condition or transformation is
imposed on `rhs`, so an independently produced actual uniform count remains
literal there. -/
theorem katzTaoSourceCap_mul_core_le_of_relativeSquare
    {delta tau : NNReal} (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) (hdeltaTau : delta ≤ tau)
    {etaKT : Real} (hetaKT : 0 < etaKT)
    {core rhs : ENNReal}
    (hscaled :
      (ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) * core ≤
        (((delta : ENNReal) / (tau : ENNReal)) ^ 2) * rhs) :
    (katzTaoDoubledFiberNatCap delta tau
        ((delta : ENNReal) ^ (-etaKT)) : ENNReal) * core ≤ rhs := by
  let C : ENNReal := (delta : ENNReal) ^ (-etaKT)
  let M := katzTaoDoubledFiberNatCap delta tau C
  let relativeSquare : ENNReal :=
    ((delta : ENNReal) / (tau : ENNReal)) ^ 2
  have htau : 0 < tau := hdelta.trans_le hdeltaTau
  have hCone : 1 ≤ C := by
    dsimp only [C]
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr hdelta)
      (ENNReal.coe_le_coe.mpr hdeltaOne) (neg_lt_zero.mpr hetaKT)
  have hCfinite : C ≠ ∞ := by
    dsimp only [C]
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hdelta.ne') ENNReal.coe_ne_top
  have hcap : (M : ENNReal) * relativeSquare ≤
      ordinaryFiberNatCapFixedConstant * C := by
    simpa only [M, C, relativeSquare] using
      katzTaoDoubledFiberNatCap_mul_relativeSquare_le_fixed
        hdelta hdeltaTau hCone hCfinite
  have hrelative0 : relativeSquare ≠ 0 := by
    dsimp only [relativeSquare]
    exact pow_ne_zero 2 (ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr hdelta.ne', ENNReal.coe_ne_top⟩)
  have hrelativeTop : relativeSquare ≠ ∞ := by
    dsimp only [relativeSquare]
    exact ENNReal.pow_ne_top
      (ENNReal.div_ne_top ENNReal.coe_ne_top
        (ENNReal.coe_ne_zero.mpr htau.ne'))
  exact sourceCap_le_of_relativeSquare M hrelative0 hrelativeTop hcap
    (by simpa only [C, relativeSquare] using hscaled)

#print axioms sourceCap_le_of_relativeSquare
#print axioms katzTaoSourceCap_mul_core_le_of_relativeSquare

end
end Family8FullRefinementSourceTauMassPopularEq46RelativeCapCancellationV3
