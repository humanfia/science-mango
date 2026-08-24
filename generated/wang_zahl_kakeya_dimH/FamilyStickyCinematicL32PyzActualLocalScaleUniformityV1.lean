import FamilyStickyCinematicL32PyzDyadicScaleMomentTransportV1

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualLocalScaleUniformityV1

open FamilyStickyCinematicL32PyzDyadicScaleMomentTransportV1

/-!
# Uniformity of the two localized scale weights

The norm and tangency maximizers may depend on the point and the chosen
centre.  Once both lie above half of the physical radius, their negative
powers are bounded by one coefficient that no longer contains either local
scale.  This is the thin physical-radius specialization of the two-scale
dyadic moment transport theorem.
-/

theorem moment_le_physical_radius_of_local_scales
    (multiplicity : Nat)
    {radius normScale tangencyScale normExponent tangencyExponent : Real}
    (hradius : 0 < radius)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hnormScale : radius / 2 < normScale)
    (htangencyScale : radius / 2 < tangencyScale)
    {lhs remaining : ENNReal}
    (hmain : lhs ≤
      (ENNReal.ofReal ((multiplicity : Real) * 2 *
        normScale ^ (-normExponent) *
        tangencyScale ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
          remaining) :
    lhs ≤
      (ENNReal.ofReal ((multiplicity : Real) * 2 *
        (2 ^ normExponent * 2 ^ tangencyExponent) *
        radius ^ (-normExponent) *
        radius ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
          remaining := by
  exact moment_le_of_selected_scales_dyadic_bins multiplicity
    hradius hradius hnormExponent htangencyExponent hnormScale
    htangencyScale hmain

#print axioms moment_le_physical_radius_of_local_scales

end FamilyStickyCinematicL32PyzActualLocalScaleUniformityV1
