import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8B2NormalizedConflictKatzTaoCapV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8B2NormalizedConflictKatzTaoCapV3

noncomputable section

/-!
# Radius-free form of the normalized Katz--Tao conflict cap

The normalized tube lower volume and the elongated test volume carry the
same squared radius.  This file cancels that common factor honestly, so the
degree cap is the fixed ceiling of `480000 * A`.
-/

theorem normalizedConflictKatzTaoRatio_eq
    {delta : NNReal} (hdeltaPos : 0 < delta)
    {A : ENNReal} (hAfinite : A ≠ ∞) :
    A * ((240000 : ENNReal) *
        ((delta / 8 : NNReal) : ENNReal) ^ 2) /
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) =
      480000 * A := by
  have hrhoPos : 0 < delta / 8 := div_pos hdeltaPos (by norm_num)
  have hrho0 : (((delta / 8 : NNReal) : ENNReal)) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hrhoPos.ne'
  have hden0 : (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨pow_ne_zero 2 hrho0, by norm_num⟩
  have hnumTop :
      A * ((240000 : ENNReal) *
        ((delta / 8 : NNReal) : ENNReal) ^ 2) ≠ ∞ := by
    apply ENNReal.mul_ne_top hAfinite
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hleftTop :
      A * ((240000 : ENNReal) *
          ((delta / 8 : NNReal) : ENNReal) ^ 2) /
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) ≠ ∞ :=
    ENNReal.div_ne_top hnumTop hden0
  have hrightTop : (480000 : ENNReal) * A ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hAfinite
  apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).mp
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_div]
  field_simp
  ring

theorem normalizedConflictKatzTaoNatCap_eq_fixed
    {delta : NNReal} (hdeltaPos : 0 < delta)
    {A : ENNReal} (hAfinite : A ≠ ∞) :
    normalizedConflictKatzTaoNatCap delta A =
      Nat.ceil ((480000 * A : ENNReal).toReal) := by
  unfold normalizedConflictKatzTaoNatCap
  rw [normalizedConflictKatzTaoRatio_eq hdeltaPos hAfinite]

theorem normalizedConflictIndices_card_le_fixedKatzTaoNatCap
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A
      (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum D).family.bodyFamily)
    (a : iota) :
    (normalizedConflictIndices D a).card <=
      Nat.ceil ((480000 * A : ENNReal).toReal) := by
  rw [← normalizedConflictKatzTaoNatCap_eq_fixed hdeltaPos hAfinite]
  exact normalizedConflictIndices_card_le_katzTaoNatCap
    D hdeltaPos hdeltaHalf hAfinite hKT a

#print axioms normalizedConflictKatzTaoRatio_eq
#print axioms normalizedConflictKatzTaoNatCap_eq_fixed
#print axioms normalizedConflictIndices_card_le_fixedKatzTaoNatCap

end
end Family8B2NormalizedConflictKatzTaoCapV5
