import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17

open Family8CanonicalLowerBufferedScaleV4
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14

noncomputable section

/-!
# Automatic side conditions for the exact-degree power envelope

The incidence-ratio `one` and `finite` hypotheses are automatic in the
canonical application.  This module derives them from `1 <= A`, the source
power cap, and the elementary scale ordering `tau <= theta`.
-/

theorem activeOwnerKatzTaoIncidenceRatio_ne_top
    {delta radius : NNReal} {A : ENNReal}
    (hdelta : 0 < delta) (hAfinite : A ≠ ∞) :
    activeOwnerKatzTaoIncidenceRatio delta radius A ≠ ∞ := by
  unfold activeOwnerKatzTaoIncidenceRatio
  have hden0 : (delta : ENNReal) ^ 2 / 2 ≠ 0 :=
    ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩
  apply ENNReal.div_ne_top _ hden0
  apply ENNReal.mul_ne_top hAfinite
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem one_le_activeOwnerKatzTaoIncidenceRatio
    {delta radius : NNReal} {A : ENNReal}
    (hdelta : 0 < delta) (hdeltaRadius : delta <= radius)
    (hAone : 1 <= A) :
    1 <= activeOwnerKatzTaoIncidenceRatio delta radius A := by
  unfold activeOwnerKatzTaoIncidenceRatio
  have hden0 : (delta : ENNReal) ^ 2 / 2 ≠ 0 :=
    ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩
  have hdenTop : (delta : ENNReal) ^ 2 / 2 ≠ ∞ :=
    ENNReal.div_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)).2
  simp only [one_mul]
  have hhalf : (delta : ENNReal) ^ 2 / 2 <=
      (delta : ENNReal) ^ 2 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    calc
      (delta : ENNReal) ^ 2 = (delta : ENNReal) ^ 2 * 1 := by simp
      _ <= (delta : ENNReal) ^ 2 * 2 :=
        mul_le_mul' le_rfl (by norm_num)
  calc
    (delta : ENNReal) ^ 2 / 2 <= (delta : ENNReal) ^ 2 := hhalf
    _ <= (radius : ENNReal) ^ 2 := by gcongr
    _ = 1 * (1 * (radius : ENNReal) ^ 2) := by simp
    _ <= A * (240000 * (radius : ENNReal) ^ 2) :=
      mul_le_mul' hAone (mul_le_mul' (by norm_num) le_rfl)

theorem canonicalLowerBufferedScale_ge_tau
    {tau theta : NNReal} (htau : 0 < tau)
    (htauTheta : tau <= theta) {epsilon : Real}
    (hepsilon : 0 <= epsilon) :
    tau <= canonicalLowerBufferedScale tau theta epsilon := by
  have hratio : 1 <= theta / tau := by
    apply (le_div_iff₀ htau).2
    simpa only [one_mul] using htauTheta
  have hratioPow : 1 <= (theta / tau) ^ epsilon := by
    have hpow := NNReal.rpow_le_rpow hratio hepsilon
    simpa only [NNReal.one_rpow] using hpow
  rw [canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon]
  have hmul : tau * 1 <= tau * (theta / tau) ^ epsilon :=
    mul_le_mul' le_rfl hratioPow
  simpa only [mul_one] using hmul

/-- The canonical B-envelope with both ceiling side conditions discharged. -/
theorem canonicalLowerBufferedScale_exactConflictDegree_le_powerEnvelope_auto
    {globalDelta tau theta : NNReal} {A : ENNReal}
    {epsilon eta absorbEta : Real}
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (htauTheta : tau <= theta) (hthetaOne : theta <= 1)
    (hepsilon : 0 <= epsilon) (habsorbEta : 0 < absorbEta)
    (hglobalThreshold :
      globalDelta <=
        activeOwnerExactDegreeSmallDeltaThreshold absorbEta)
    (hAone : 1 <= A)
    (hA : A <= (globalDelta : ENNReal) ^ (-eta)) :
    ((1 +
        katzTaoDoubledFiberNatCap tau
            (canonicalLowerBufferedScale tau theta epsilon) A *
          katzTaoDoubledParentsNatCap tau
            (canonicalLowerBufferedScale tau theta epsilon) A : Nat) :
        ENNReal) <=
      (globalDelta : ENNReal) ^
        (-activeOwnerExactDegreePowerEnvelope epsilon eta absorbEta) := by
  have htau : 0 < tau := hglobal.trans_le hglobalTau
  have hradius : tau <=
      canonicalLowerBufferedScale tau theta epsilon :=
    canonicalLowerBufferedScale_ge_tau htau htauTheta hepsilon
  have hAfinite : A ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hA
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hglobal.ne') ENNReal.coe_ne_top
  have hratioOne :
      1 <= activeOwnerKatzTaoIncidenceRatio tau
        (canonicalLowerBufferedScale tau theta epsilon) A :=
    one_le_activeOwnerKatzTaoIncidenceRatio htau hradius hAone
  have hratioFinite :
      activeOwnerKatzTaoIncidenceRatio tau
        (canonicalLowerBufferedScale tau theta epsilon) A ≠ ∞ :=
    activeOwnerKatzTaoIncidenceRatio_ne_top htau hAfinite
  exact canonicalLowerBufferedScale_exactConflictDegree_le_powerEnvelope
    hglobal hglobalTau hthetaOne hepsilon habsorbEta hglobalThreshold
      hratioOne hratioFinite hA

#print axioms activeOwnerKatzTaoIncidenceRatio_ne_top
#print axioms one_le_activeOwnerKatzTaoIncidenceRatio
#print axioms canonicalLowerBufferedScale_ge_tau
#print axioms canonicalLowerBufferedScale_exactConflictDegree_le_powerEnvelope_auto

end
end Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
