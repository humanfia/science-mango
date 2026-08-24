import FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32ActualProjectedNormCellRadiusDominanceV1

open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1

noncomputable section

universe u v

/-!
# The norm-cell upper endpoint dominates the physical radius

This is the small dependent-ceiling bridge needed before selecting the
tangency scale.  It uses the literal actual norm maximizer bounds; the
critical exponent is never reconstructed from an unfolded maximizer term.
-/

theorem radius_le_dyadicUpper_of_nonempty_actual_norm_cell
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    (normCeiling normExponent : Real)
    (hnormCeiling : (radius : Real) ≤ normCeiling)
    (label : Int)
    (E : Set point)
    (hE : E.Nonempty)
    (hfamily : ∀ x ∈ E,
      (actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint x)).Nonempty)
    (hbin : ∀ x ∈ E,
      actualProjectedAmbientNormScale fine physical normCeiling normExponent x
        ≤ dyadicCeilUpper label) :
    (radius : Real) ≤ dyadicCeilUpper label := by
  obtain ⟨x, hx⟩ := hE
  exact
    (actualProjectedAmbientNormScale_bounds fine physical hnormCeiling x
      (hfamily x hx)).1.trans (hbin x hx)

#print axioms radius_le_dyadicUpper_of_nonempty_actual_norm_cell

end

end FamilyStickyCinematicL32ActualProjectedNormCellRadiusDominanceV1
