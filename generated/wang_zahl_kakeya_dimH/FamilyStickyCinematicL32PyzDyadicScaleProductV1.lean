import FamilyStickyCinematicL32PyzDyadicNegativeRpowComparisonV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32PyzDyadicScaleProductV1

open FamilyStickyCinematicL32PyzDyadicNegativeRpowComparisonV1

/-! Exact product form of the two PYZ half-bin scale comparisons. -/

theorem selected_negative_rpow_product_le_dyadic_uppers
    {normSelected normUpper tangencySelected tangencyUpper
      normExponent tangencyExponent : Real}
    (hnormUpper : 0 < normUpper)
    (htangencyUpper : 0 < tangencyUpper)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hnormBin : normUpper / 2 < normSelected)
    (htangencyBin : tangencyUpper / 2 < tangencySelected) :
    normSelected ^ (-normExponent) *
        tangencySelected ^ (-tangencyExponent) ≤
      (2 ^ normExponent * 2 ^ tangencyExponent) *
        (normUpper ^ (-normExponent) *
          tangencyUpper ^ (-tangencyExponent)) := by
  have hn := rpow_neg_le_two_rpow_mul_of_half_lt hnormUpper
    hnormExponent hnormBin
  have ht := rpow_neg_le_two_rpow_mul_of_half_lt htangencyUpper
    htangencyExponent htangencyBin
  have htangencySelected : 0 < tangencySelected :=
    (div_pos htangencyUpper (by norm_num)).trans htangencyBin
  have htwoNorm : (0 : Real) ≤ 2 ^ normExponent :=
    Real.rpow_nonneg (by norm_num) _
  have hnormUpperPow : 0 ≤ normUpper ^ (-normExponent) :=
    Real.rpow_nonneg hnormUpper.le _
  calc
    normSelected ^ (-normExponent) *
        tangencySelected ^ (-tangencyExponent) ≤
      (2 ^ normExponent * normUpper ^ (-normExponent)) *
        (2 ^ tangencyExponent *
          tangencyUpper ^ (-tangencyExponent)) := by
      exact mul_le_mul hn ht
        (Real.rpow_nonneg htangencySelected.le _)
        (mul_nonneg htwoNorm hnormUpperPow)
    _ = (2 ^ normExponent * 2 ^ tangencyExponent) *
        (normUpper ^ (-normExponent) *
          tangencyUpper ^ (-tangencyExponent)) := by ring

#print axioms selected_negative_rpow_product_le_dyadic_uppers

end FamilyStickyCinematicL32PyzDyadicScaleProductV1
