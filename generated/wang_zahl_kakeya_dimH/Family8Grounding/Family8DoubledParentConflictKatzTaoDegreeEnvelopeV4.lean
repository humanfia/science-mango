import Family8Grounding.Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8DoubledParentConflictKatzTaoDegreeEnvelopeV4

open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
open Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2

noncomputable section

/-!
# A ceiling-free envelope for the sharp doubled-parent degree

Both genuine incidence caps are ceilings of the same finite Katz--Tao mass
ratio. Replacing each ceiling by `ratio + 1` keeps the full
`rho^4 / delta^4` scale gain visible; in particular, this module never
flattens that ratio to the coarse `delta^-4` fallback.
-/

def katzTaoIncidenceRatio
    (delta rho : NNReal) (A : ENNReal) : ENNReal :=
  A * ((240000 : ENNReal) * (rho : ENNReal) ^ 2) /
    ((delta : ENNReal) ^ 2 / 2)

def katzTaoDoubledParentConflictEnvelope
    (delta rho : NNReal) (A : ENNReal) : ENNReal :=
  1 + (katzTaoIncidenceRatio delta rho A + 1) *
    (katzTaoIncidenceRatio delta rho A + 1)

theorem katzTaoIncidenceRatio_ne_top
    {delta rho : NNReal} {A : ENNReal}
    (hdelta : 0 < delta) (hAfinite : A ≠ ∞) :
    katzTaoIncidenceRatio delta rho A ≠ ∞ := by
  unfold katzTaoIncidenceRatio
  apply ENNReal.div_ne_top
  · apply ENNReal.mul_ne_top hAfinite
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  · exact ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩

theorem katzTaoDoubledFiberNatCap_coe_le_ratio_add_one
    {delta rho : NNReal} {A : ENNReal}
    (hdelta : 0 < delta) (hAfinite : A ≠ ∞) :
    (katzTaoDoubledFiberNatCap delta rho A : ENNReal) ≤
      katzTaoIncidenceRatio delta rho A + 1 := by
  let q := katzTaoIncidenceRatio delta rho A
  have hqTop : q ≠ ∞ := katzTaoIncidenceRatio_ne_top hdelta hAfinite
  have hrightTop : q + 1 ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hqTop, by simp⟩
  apply (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hrightTop).mp
  rw [ENNReal.toReal_add hqTop (by simp)]
  norm_cast
  simpa only [katzTaoDoubledFiberNatCap, q,
    katzTaoIncidenceRatio, ENNReal.toReal_natCast,
    ENNReal.toReal_one] using
      (Nat.ceil_lt_add_one (ENNReal.toReal_nonneg :
        0 ≤ (katzTaoIncidenceRatio delta rho A).toReal)).le

theorem katzTaoDoubledParentsNatCap_coe_le_ratio_add_one
    {delta rho : NNReal} {A : ENNReal}
    (hdelta : 0 < delta) (hAfinite : A ≠ ∞) :
    (katzTaoDoubledParentsNatCap delta rho A : ENNReal) ≤
      katzTaoIncidenceRatio delta rho A + 1 := by
  simpa only [katzTaoDoubledParentsNatCap,
    katzTaoDoubledFiberNatCap] using
    katzTaoDoubledFiberNatCap_coe_le_ratio_add_one
      (delta := delta) (rho := rho) (A := A) hdelta hAfinite

/-- The exact graph loss is bounded by a ceiling-free expression retaining
the sharp fourth power of the relative scale. -/
theorem katzTaoDoubledParentConflictBudget_le_envelope
    {delta rho : NNReal} {A : ENNReal}
    (hdelta : 0 < delta) (hAfinite : A ≠ ∞) :
    katzTaoDoubledParentConflictBudget delta rho A ≤
      katzTaoDoubledParentConflictEnvelope delta rho A := by
  have hfiber :=
    katzTaoDoubledFiberNatCap_coe_le_ratio_add_one
      (delta := delta) (rho := rho) (A := A) hdelta hAfinite
  have hparents :=
    katzTaoDoubledParentsNatCap_coe_le_ratio_add_one
      (delta := delta) (rho := rho) (A := A) hdelta hAfinite
  unfold katzTaoDoubledParentConflictBudget
    katzTaoDoubledParentConflictEnvelope
  push_cast
  exact add_le_add le_rfl (mul_le_mul' hfiber hparents)

#print axioms katzTaoIncidenceRatio_ne_top
#print axioms katzTaoDoubledFiberNatCap_coe_le_ratio_add_one
#print axioms katzTaoDoubledParentsNatCap_coe_le_ratio_add_one
#print axioms katzTaoDoubledParentConflictBudget_le_envelope

end

end Family8DoubledParentConflictKatzTaoDegreeEnvelopeV4
