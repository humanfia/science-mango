import FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false

open MeasureTheory

namespace FamilyStickyCinematicL32ContinuumDyadicCeilBucketMeasurableV1

open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# Measurability of the actual ceil-log dyadic label

This proves measurability of the label operation itself.  Consequently, the
only source-specific measurability obligation in a continuum critical-scale
selection is measurability of the real-valued critical scale map.
-/

/-- The literal label `ceil (log_2 r)` is measurable on all of `Real`.
No positivity premise is needed for measurability. -/
theorem measurable_dyadicCeilBucket :
    Measurable dyadicCeilBucket := by
  change Measurable (fun r : Real => ⌈Real.log r / Real.log 2⌉)
  exact (Real.measurable_log.div_const (Real.log 2)).ceil

/-- Composition with a measurable real-valued scale preserves
measurability of the dyadic label. -/
theorem Measurable.dyadicCeilBucket
    {X : Type*} [MeasurableSpace X] {scale : X → Real}
    (hscale : Measurable scale) :
    Measurable (fun x => dyadicCeilBucket (scale x)) :=
  measurable_dyadicCeilBucket.comp hscale

#print axioms measurable_dyadicCeilBucket
#print axioms Measurable.dyadicCeilBucket

end

end FamilyStickyCinematicL32ContinuumDyadicCeilBucketMeasurableV1
