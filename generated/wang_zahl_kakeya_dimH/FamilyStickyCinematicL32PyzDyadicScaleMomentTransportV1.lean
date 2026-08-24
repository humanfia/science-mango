import FamilyStickyCinematicL32PyzDyadicScaleProductV1
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32PyzDyadicScaleMomentTransportV1

open FamilyStickyCinematicL32PyzDyadicScaleProductV1

/-!
# Weighted moment transport to the two dyadic upper scales

This module changes only the two selected negative scale powers.  All
constants remain literal, including the two half-bin losses.
-/

theorem weighted_selected_scales_le_dyadic_uppers
    (multiplicity : Nat)
    {normSelected normUpper tangencySelected tangencyUpper
      normExponent tangencyExponent : Real}
    (hnormUpper : 0 < normUpper)
    (htangencyUpper : 0 < tangencyUpper)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hnormBin : normUpper / 2 < normSelected)
    (htangencyBin : tangencyUpper / 2 < tangencySelected) :
    (multiplicity : Real) * 2 * normSelected ^ (-normExponent) *
        tangencySelected ^ (-tangencyExponent) ≤
      (multiplicity : Real) * 2 *
        (2 ^ normExponent * 2 ^ tangencyExponent) *
        normUpper ^ (-normExponent) *
        tangencyUpper ^ (-tangencyExponent) := by
  have hscale := selected_negative_rpow_product_le_dyadic_uppers
    hnormUpper htangencyUpper hnormExponent htangencyExponent hnormBin
    htangencyBin
  calc
    (multiplicity : Real) * 2 * normSelected ^ (-normExponent) *
        tangencySelected ^ (-tangencyExponent) =
      ((multiplicity : Real) * 2) *
        (normSelected ^ (-normExponent) *
          tangencySelected ^ (-tangencyExponent)) := by ring
    _ ≤ ((multiplicity : Real) * 2) *
        ((2 ^ normExponent * 2 ^ tangencyExponent) *
          (normUpper ^ (-normExponent) *
            tangencyUpper ^ (-tangencyExponent))) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (multiplicity : Real) * 2 *
        (2 ^ normExponent * 2 ^ tangencyExponent) *
        normUpper ^ (-normExponent) *
        tangencyUpper ^ (-tangencyExponent) := by ring

theorem moment_le_of_selected_scales_dyadic_bins
    (multiplicity : Nat)
    {normSelected normUpper tangencySelected tangencyUpper
      normExponent tangencyExponent : Real}
    (hnormUpper : 0 < normUpper)
    (htangencyUpper : 0 < tangencyUpper)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hnormBin : normUpper / 2 < normSelected)
    (htangencyBin : tangencyUpper / 2 < tangencySelected)
    {lhs remaining : ENNReal}
    (hmain : lhs ≤
      (ENNReal.ofReal ((multiplicity : Real) * 2 *
        normSelected ^ (-normExponent) *
        tangencySelected ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
          remaining) :
    lhs ≤
      (ENNReal.ofReal ((multiplicity : Real) * 2 *
        (2 ^ normExponent * 2 ^ tangencyExponent) *
        normUpper ^ (-normExponent) *
        tangencyUpper ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
          remaining := by
  have hweighted := weighted_selected_scales_le_dyadic_uppers multiplicity
    hnormUpper htangencyUpper hnormExponent htangencyExponent hnormBin
    htangencyBin
  have hrpow := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hweighted)
    (by norm_num : (0 : Real) ≤ 3 / 2)
  exact hmain.trans (mul_le_mul_left hrpow remaining)

#print axioms weighted_selected_scales_le_dyadic_uppers
#print axioms moment_le_of_selected_scales_dyadic_bins

end FamilyStickyCinematicL32PyzDyadicScaleMomentTransportV1
