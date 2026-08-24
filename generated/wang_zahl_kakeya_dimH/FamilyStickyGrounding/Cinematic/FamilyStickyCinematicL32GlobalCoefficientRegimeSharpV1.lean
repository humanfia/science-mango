import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32JetSeparationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32LocalTangencyV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1

/-!
# Sharpened global coefficient regimes

This is the constant-compatible version of the global Wang--Zahl trace
trichotomy.  The explicit formulas allow coefficient thresholds `4` and
`8`, improving the uniform second-jet constant to `1/45`.  These constants
are sufficient for the fixed rectangle constant in PYZ Lemma 5.3.
-/

private theorem abs_main_sub_error_le_abs_sum (main error : Real) :
    |main| - |error| <= |main + error| := by
  have htriangle := abs_add_le (main + error) (-error)
  rw [add_neg_cancel_right, abs_neg] at htriangle
  linarith

/-- Four-times constant-coefficient dominance already separates the value
jet by half the constant coefficient. -/
theorem traceJet0_large_of_four_constant_dominates
    (da db dd ft t : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2)
    (ha : 4 * (|db| + |dd|) <= |da|) :
    |da| / 2 <= |traceJet0 da db dd ft t| := by
  have hdb : |db * ft| <= 2 * |db| := by
    rw [abs_mul]
    nlinarith [abs_nonneg db]
  have hdd : |dd * t * ft| <= 2 * |dd| := by
    rw [abs_mul, abs_mul]
    have hdt : |dd| * |t| <= |dd| := by
      nlinarith [abs_nonneg dd, abs_nonneg t]
    have hdt0 : 0 <= |dd| * |t| :=
      mul_nonneg (abs_nonneg dd) (abs_nonneg t)
    calc
      |dd| * |t| * |ft| <= (|dd| * |t|) * 2 :=
        mul_le_mul_of_nonneg_left hft hdt0
      _ <= |dd| * 2 := mul_le_mul_of_nonneg_right hdt (by norm_num)
      _ = 2 * |dd| := by ring
  have herror : |db * ft + dd * t * ft| <=
      2 * (|db| + |dd|) := by
    calc
      |db * ft + dd * t * ft| <= |db * ft| + |dd * t * ft| :=
        abs_add_le _ _
      _ <= 2 * |db| + 2 * |dd| := add_le_add hdb hdd
      _ = 2 * (|db| + |dd|) := by ring
  have hreverse := abs_main_sub_error_le_abs_sum
    da (db * ft + dd * t * ft)
  rw [traceJet0, add_assoc]
  nlinarith [abs_nonneg da]

/-- Eight-times linear-coefficient dominance separates the first jet by
half the linear coefficient. -/
theorem traceJet1_large_of_eight_linear_dominates
    (db dd ft f1 t : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2)
    (hf1Lower : 1 <= |f1|) (hf1Upper : |f1| <= 2)
    (hb : 8 * |dd| <= |db|) :
    |db| / 2 <= |traceJet1 db dd ft f1 t| := by
  have htf1 : |t * f1| <= 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg t, abs_nonneg f1]
  have hinside : |ft + t * f1| <= 4 := by
    calc
      |ft + t * f1| <= |ft| + |t * f1| := abs_add_le _ _
      _ <= 4 := by linarith
  have herror : |dd * (ft + t * f1)| <= 4 * |dd| := by
    rw [abs_mul]
    nlinarith [abs_nonneg dd]
  have hmain : |db| <= |db * f1| := by
    rw [abs_mul]
    nlinarith [abs_nonneg db]
  have hreverse := abs_main_sub_error_le_abs_sum
    (db * f1) (dd * (ft + t * f1))
  rw [traceJet1]
  nlinarith [abs_nonneg db, abs_nonneg dd]

/-- Sharpened global trichotomy: the value, first, or second jet is
uniformly separated by an explicit fraction of coefficient distance. -/
theorem global_value_or_first_or_second_jet_separation_sharp
    (da db dd : Real) :
    (forall ft t : Real, |t| <= 1 -> |ft| <= 2 ->
      coefficientDistance da db dd / 3 <=
        |traceJet0 da db dd ft t|) ∨
    (forall ft f1 t : Real, |t| <= 1 -> |ft| <= 2 ->
      1 <= |f1| -> |f1| <= 2 ->
      coefficientDistance da db dd / 12 <=
        |traceJet1 db dd ft f1 t|) ∨
    (forall f1 f2 t : Real, |t| <= 1 -> 1 <= |f1| ->
      |f2| <= 1 / 100 ->
      coefficientDistance da db dd / 45 <
        |traceJet2 db dd f1 f2 t|) := by
  by_cases ha : 4 * (|db| + |dd|) <= |da|
  · left
    intro ft t ht hft
    have hjet := traceJet0_large_of_four_constant_dominates
      da db dd ft t ht hft ha
    rw [coefficientDistance]
    nlinarith [abs_nonneg da, abs_nonneg db, abs_nonneg dd]
  · have ha' : |da| < 4 * (|db| + |dd|) := lt_of_not_ge ha
    by_cases hb : 8 * |dd| <= |db|
    · right
      left
      intro ft f1 t ht hft hf1Lower hf1Upper
      have hjet := traceJet1_large_of_eight_linear_dominates
        db dd ft f1 t ht hft hf1Lower hf1Upper hb
      rw [coefficientDistance]
      nlinarith [abs_nonneg da, abs_nonneg db, abs_nonneg dd]
    · right
      right
      have hb' : |db| < 8 * |dd| := lt_of_not_ge hb
      have hddPos : 0 < |dd| := by
        nlinarith [abs_nonneg db]
      have hbTen : |db| < 10 * |dd| := by
        nlinarith
      intro f1 f2 t ht hf1Lower hf2
      have hjet := traceJet2_large_of_quadratic_dominates
        db dd f1 f2 t ht hf1Lower hf2 hbTen
      rw [coefficientDistance]
      nlinarith [abs_nonneg da, abs_nonneg db, abs_nonneg dd]

#print axioms traceJet0_large_of_four_constant_dominates
#print axioms traceJet1_large_of_eight_linear_dominates
#print axioms global_value_or_first_or_second_jet_separation_sharp

end FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
