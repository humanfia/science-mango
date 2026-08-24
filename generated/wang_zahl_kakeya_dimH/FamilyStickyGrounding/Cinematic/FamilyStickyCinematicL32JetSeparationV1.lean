import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FamilyStickyCinematicL32JetSeparationV1

/-!
# Jet separation for the Wang--Zahl cinematic family

Provenance: Wang--Zahl, *Sticky Kakeya sets and the sticky Kakeya
conjecture*, arXiv:2210.09581, Definition 7.1 and Lemma 7.3; equivalently
the final manuscript's Section 7, equations `defnGabd` and `bigInf`.

This is the elementary, pointwise producer in the verification that

`g_(a,b,d)(t) = a + b f(t) + d t f(t)`

is a cinematic family.  It proves the quantitative separation of the
zero-, first-, and second-order jets directly from the coefficient
differences.  It does not assume the Pramanik--Yang--Zahl maximal estimate,
the cinematic-family conclusion, or an equivalent projection bound.
-/

/-- Value of the coefficient-difference trace at one parameter. -/
def traceJet0 (da db dd ft t : Real) : Real :=
  da + db * ft + dd * t * ft

/-- First derivative of the coefficient-difference trace, expressed in
terms of the value and first derivative of the base function. -/
def traceJet1 (db dd ft f1 t : Real) : Real :=
  db * f1 + dd * (ft + t * f1)

/-- Second derivative of the coefficient-difference trace, expressed in
terms of the first two derivatives of the base function. -/
def traceJet2 (db dd f1 f2 t : Real) : Real :=
  db * f2 + dd * (2 * f1 + t * f2)

/-- Reverse triangle inequality in the form used for each jet. -/
private theorem abs_sub_error_le_abs_add (x e : Real) :
    |x| - |e| <= |x + e| := by
  have h := abs_add_le (x + e) (-e)
  rw [add_neg_cancel_right, abs_neg] at h
  linarith

/-- The value jet separates the constant coefficient whenever it dominates
the two remaining coefficients. -/
theorem traceJet0_large_of_constant_dominates
    (da db dd ft t : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2)
    (ha : 10 * (|db| + |dd|) <= |da|) :
    |da| / 2 <= |traceJet0 da db dd ft t| := by
  have hdb : |db * ft| <= 2 * |db| := by
    rw [abs_mul]
    nlinarith [abs_nonneg db]
  have hdd : |dd * t * ft| <= 2 * |dd| := by
    rw [abs_mul, abs_mul]
    have ht0 : 0 <= |t| := abs_nonneg t
    have hdd0 : 0 <= |dd| := abs_nonneg dd
    have hprod : |dd| * |t| <= |dd| := by nlinarith
    have hprod0 : 0 <= |dd| * |t| := mul_nonneg hdd0 ht0
    calc
      |dd| * |t| * |ft| <= (|dd| * |t|) * 2 :=
        mul_le_mul_of_nonneg_left hft hprod0
      _ <= |dd| * 2 := mul_le_mul_of_nonneg_right hprod (by norm_num)
      _ = 2 * |dd| := by ring
  have herr : |db * ft + dd * t * ft| <=
      2 * (|db| + |dd|) := by
    calc
      |db * ft + dd * t * ft| <= |db * ft| + |dd * t * ft| :=
        abs_add_le _ _
      _ <= 2 * |db| + 2 * |dd| := add_le_add hdb hdd
      _ = 2 * (|db| + |dd|) := by ring
  have hreverse := abs_sub_error_le_abs_add da (db * ft + dd * t * ft)
  rw [traceJet0]
  rw [add_assoc]
  nlinarith [abs_nonneg db, abs_nonneg dd]

/-- The first jet separates the `b` coefficient whenever `b` dominates
`d`. -/
theorem traceJet1_large_of_linear_dominates
    (db dd ft f1 t : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2)
    (hf1Lower : 1 <= |f1|) (hf1Upper : |f1| <= 2)
    (hb : 10 * |dd| <= |db|) :
    |db| / 2 <= |traceJet1 db dd ft f1 t| := by
  have htf1 : |t * f1| <= 2 := by
    rw [abs_mul]
    have ht0 : 0 <= |t| := abs_nonneg t
    nlinarith
  have hinside : |ft + t * f1| <= 4 := by
    calc
      |ft + t * f1| <= |ft| + |t * f1| := abs_add_le _ _
      _ <= 4 := by linarith
  have herr : |dd * (ft + t * f1)| <= 4 * |dd| := by
    rw [abs_mul]
    have hdd0 : 0 <= |dd| := abs_nonneg dd
    nlinarith
  have hmain : |db| <= |db * f1| := by
    rw [abs_mul]
    have hdb0 : 0 <= |db| := abs_nonneg db
    nlinarith
  have hreverse :=
    abs_sub_error_le_abs_add (db * f1) (dd * (ft + t * f1))
  rw [traceJet1]
  nlinarith [abs_nonneg dd]

/-- The second jet separates the `d` coefficient whenever `b` does not
dominate `d`.  The factor `2 f'` in the exact second derivative leaves ample
room for the `1/100` curvature error. -/
theorem traceJet2_large_of_quadratic_dominates
    (db dd f1 f2 t : Real)
    (ht : |t| <= 1) (hf1Lower : 1 <= |f1|)
    (hf2 : |f2| <= 1 / 100)
    (hb : |db| < 10 * |dd|) :
    |dd| <= |traceJet2 db dd f1 f2 t| := by
  have hdt : |dd * t| <= |dd| := by
    rw [abs_mul]
    have hdd0 : 0 <= |dd| := abs_nonneg dd
    nlinarith [abs_nonneg t]
  have hcoeff : |db + dd * t| < 11 * |dd| := by
    calc
      |db + dd * t| <= |db| + |dd * t| := abs_add_le _ _
      _ < 10 * |dd| + |dd| := add_lt_add_of_lt_of_le hb hdt
      _ = 11 * |dd| := by ring
  have herror : |(db + dd * t) * f2| < (11 / 100 : Real) * |dd| := by
    rw [abs_mul]
    have hc0 : 0 <= |db + dd * t| := abs_nonneg _
    calc
      |db + dd * t| * |f2| <= |db + dd * t| * (1 / 100 : Real) :=
        mul_le_mul_of_nonneg_left hf2 hc0
      _ < (11 * |dd|) * (1 / 100 : Real) :=
        mul_lt_mul_of_pos_right hcoeff (by norm_num)
      _ = (11 / 100 : Real) * |dd| := by ring
  have hmain : 2 * |dd| <= |2 * dd * f1| := by
    rw [abs_mul, abs_mul]
    norm_num
    have hdd0 : 0 <= |dd| := abs_nonneg dd
    calc
      2 * |dd| = (2 * |dd|) * 1 := by ring
      _ <= (2 * |dd|) * |f1| :=
        mul_le_mul_of_nonneg_left hf1Lower (mul_nonneg (by norm_num) hdd0)
  have hrewrite :
      traceJet2 db dd f1 f2 t =
        2 * dd * f1 + (db + dd * t) * f2 := by
    simp [traceJet2]
    ring
  rw [hrewrite]
  have hreverse :=
    abs_sub_error_le_abs_add (2 * dd * f1) ((db + dd * t) * f2)
  have hdd0 : 0 <= |dd| := abs_nonneg dd
  nlinarith

/-- Quantitative pointwise jet separation used in Wang--Zahl Lemma 7.3.
At every parameter, one of the three jets controls the full coefficient
distance; summing their absolute values gives the displayed cinematic
nondegeneracy bound. -/
theorem cinematic_trace_jet_separation
    (da db dd ft f1 f2 t : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2)
    (hf1Lower : 1 <= |f1|) (hf1Upper : |f1| <= 2)
    (hf2 : |f2| <= 1 / 100) :
    (1 / 200 : Real) * (|da| + |db| + |dd|) <=
      |traceJet0 da db dd ft t| +
        |traceJet1 db dd ft f1 t| +
          |traceJet2 db dd f1 f2 t| := by
  by_cases ha : 10 * (|db| + |dd|) <= |da|
  · have hjet := traceJet0_large_of_constant_dominates
      da db dd ft t ht hft ha
    have hrest : |db| + |dd| <= |da| / 10 := by linarith
    have hnonneg1 := abs_nonneg (traceJet1 db dd ft f1 t)
    have hnonneg2 := abs_nonneg (traceJet2 db dd f1 f2 t)
    nlinarith [abs_nonneg da]
  · have ha' : |da| < 10 * (|db| + |dd|) := lt_of_not_ge ha
    by_cases hb : 10 * |dd| <= |db|
    · have hjet := traceJet1_large_of_linear_dominates
        db dd ft f1 t ht hft hf1Lower hf1Upper hb
      have hdd : |dd| <= |db| / 10 := by linarith
      have hnonneg0 := abs_nonneg (traceJet0 da db dd ft t)
      have hnonneg2 := abs_nonneg (traceJet2 db dd f1 f2 t)
      nlinarith [abs_nonneg db]
    · have hb' : |db| < 10 * |dd| := lt_of_not_ge hb
      have hjet := traceJet2_large_of_quadratic_dominates
        db dd f1 f2 t ht hf1Lower hf2 hb'
      have hnonneg0 := abs_nonneg (traceJet0 da db dd ft t)
      have hnonneg1 := abs_nonneg (traceJet1 db dd ft f1 t)
      nlinarith [abs_nonneg dd]

#print axioms traceJet0_large_of_constant_dominates
#print axioms traceJet1_large_of_linear_dominates
#print axioms traceJet2_large_of_quadratic_dominates
#print axioms cinematic_trace_jet_separation

end FamilyStickyCinematicL32JetSeparationV1
