import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32OscillationProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceTangencyMinimizerV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32TraceTangencyScaleUpperV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1

/-!
# Upper normalization of the trace tangency parameter

Provenance: the elementary normalization `Delta(f,g) <= ||f-g||` used in
Pramanik--Yang--Zahl, arXiv:2207.02259v3, Definition 3.7 and Lemma 3.8,
with explicit constants for the Wang--Zahl Lemma 7.3 trace.
-/

/-- On the normalized parameter range, the value jet is at most twice the
coefficient distance. -/
theorem abs_traceJet0_le_two_coefficientDistance
    (da db dd ft t : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2) :
    |traceJet0 da db dd ft t| <=
      2 * coefficientDistance da db dd := by
  have hlinear : |db * ft| <= 2 * |db| := by
    rw [abs_mul]
    calc
      |db| * |ft| <= |db| * 2 :=
        mul_le_mul_of_nonneg_left hft (abs_nonneg db)
      _ = 2 * |db| := by ring
  have hparameterProduct : |t * ft| <= 2 := by
    rw [abs_mul]
    have htNonneg : 0 <= |t| := abs_nonneg t
    calc
      |t| * |ft| <= |t| * 2 :=
        mul_le_mul_of_nonneg_left hft htNonneg
      _ <= 1 * 2 := mul_le_mul_of_nonneg_right ht (by norm_num)
      _ = 2 := by norm_num
  have hparameterProductAbs : |t| * |ft| <= 2 := by
    simpa [abs_mul] using hparameterProduct
  have hquadratic : |dd * t * ft| <= 2 * |dd| := by
    rw [abs_mul, abs_mul]
    calc
      |dd| * |t| * |ft| = |dd| * (|t| * |ft|) := by ring
      _ <= |dd| * 2 :=
        mul_le_mul_of_nonneg_left hparameterProductAbs (abs_nonneg dd)
      _ = 2 * |dd| := by ring
  calc
    |traceJet0 da db dd ft t| <=
        |da| + |db * ft| + |dd * t * ft| := by
      rw [traceJet0]
      calc
        |da + db * ft + dd * t * ft| <=
            |da + db * ft| + |dd * t * ft| := abs_add_le _ _
        _ <= (|da| + |db * ft|) + |dd * t * ft| :=
          add_le_add (abs_add_le _ _) le_rfl
    _ <= |da| + 2 * |db| + 2 * |dd| := by
      gcongr
    _ <= 2 * coefficientDistance da db dd := by
      rw [coefficientDistance]
      nlinarith [abs_nonneg da]

/-- The actual value--slope cost is at most six times the coefficient
distance. -/
theorem traceTangencyCost_le_six_coefficientDistance
    (f f1 : Real -> Real) (da db dd theta : Real)
    (htheta : |theta| <= 1) (hft : |f theta| <= 2)
    (hf1 : |f1 theta| <= 2) :
    traceTangencyCost f f1 da db dd theta <=
      6 * coefficientDistance da db dd := by
  have hvalue := abs_traceJet0_le_two_coefficientDistance
    da db dd (f theta) theta htheta hft
  have hslope := abs_traceJet1_le_four_coefficientDistance
    da db dd (f theta) (f1 theta) theta htheta hft hf1
  calc
    traceTangencyCost f f1 da db dd theta =
        |traceJet0 da db dd (f theta) theta| +
          |traceJet1 db dd (f theta) (f1 theta) theta| := by
      rfl
    _ <= 2 * coefficientDistance da db dd +
        4 * coefficientDistance da db dd := add_le_add hvalue hslope
    _ = 6 * coefficientDistance da db dd := by ring

/-- An explicitly attained trace tangency parameter inherits the six-times
coefficient-distance upper bound. -/
theorem attained_traceTangencyParameter_le_six_coefficientDistance
    (f f1 : Real -> Real) (da db dd Delta thetaDelta : Real)
    (hDeltaDef :
      Delta = traceTangencyCost f f1 da db dd thetaDelta)
    (htheta : |thetaDelta| <= 1) (hft : |f thetaDelta| <= 2)
    (hf1 : |f1 thetaDelta| <= 2) :
    Delta <= 6 * coefficientDistance da db dd := by
  rw [hDeltaDef]
  exact traceTangencyCost_le_six_coefficientDistance
    f f1 da db dd thetaDelta htheta hft hf1

#print axioms abs_traceJet0_le_two_coefficientDistance
#print axioms traceTangencyCost_le_six_coefficientDistance
#print axioms attained_traceTangencyParameter_le_six_coefficientDistance

end FamilyStickyCinematicL32TraceTangencyScaleUpperV1
