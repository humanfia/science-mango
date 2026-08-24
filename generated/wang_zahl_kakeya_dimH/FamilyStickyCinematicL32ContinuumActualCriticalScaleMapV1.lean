import FamilyStickyCinematicL32ContinuumDyadicCeilBucketMeasurableV1
import FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1

open FamilyStickyCinematicL32ContinuumDyadicCeilBucketMeasurableV1
open FamilyStickyCinematicL32Lemma57CanonicalMaximizerV1
open FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# The actual pointwise critical scale and its measurability boundary

The critical maximizer already supplies its scale bounds pointwise.  This
module extends that scale by the lower endpoint outside the continuum source
set, so it is an honest total function to which measurable-selection applies.
No measurability is claimed from the present geometric source API: the
`activeAtPoint`/finite-family maps currently carry no measurable structure.
-/

universe u v

variable {X : Type u} {alpha : Type v} [MeasurableSpace X]

/-- The actual canonical maximizer scale, expressed directly through the V1
finite critical carrier and canonical finite maximizer. -/
noncomputable def finiteCriticalMaximizerScale
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (delta ceiling exponent : Real) (hfamily : family.Nonempty) : Real :=
  (canonicalMaximizerData family
    (finiteCriticalScaleCarrier family distance delta ceiling)
    distance exponent
    (finiteCriticalScaleCarrier_nonempty family distance delta ceiling)
    hfamily).scale

theorem finiteCriticalMaximizerScale_bounds
    (family : Finset alpha) (distance : alpha → alpha → Real)
    {delta ceiling exponent : Real} (hfamily : family.Nonempty)
    (hdeltaCeiling : delta ≤ ceiling) :
    delta ≤ finiteCriticalMaximizerScale family distance delta ceiling
        exponent hfamily ∧
      finiteCriticalMaximizerScale family distance delta ceiling
        exponent hfamily ≤ ceiling := by
  exact finiteCriticalScaleCarrier_bounds family distance hdeltaCeiling
    (canonicalMaximizerData_scale_mem family
      (finiteCriticalScaleCarrier family distance delta ceiling)
      distance exponent
      (finiteCriticalScaleCarrier_nonempty family distance delta ceiling)
      hfamily)

/-- The actual canonical critical-maximizer scale on `E`, extended by `delta`
off `E`. -/
noncomputable def actualCriticalScaleOn
    (E : Set X) (family : X → Finset alpha)
    (distance : X → alpha → alpha → Real)
    (delta ceiling exponent : Real)
    (hfamily : ∀ x ∈ E, (family x).Nonempty) : X → Real :=
  by
    classical
    exact fun x => if hx : x ∈ E then
      finiteCriticalMaximizerScale (family x) (distance x)
        delta ceiling exponent (hfamily x hx)
    else delta

omit [MeasurableSpace X] in
theorem actualCriticalScaleOn_eq
    (E : Set X) (family : X → Finset alpha)
    (distance : X → alpha → alpha → Real)
    (delta ceiling exponent : Real)
    (hfamily : ∀ x ∈ E, (family x).Nonempty)
    {x : X} (hx : x ∈ E) :
    actualCriticalScaleOn E family distance delta ceiling exponent
        hfamily x =
      finiteCriticalMaximizerScale (family x) (distance x)
        delta ceiling exponent (hfamily x hx) := by
  simp only [actualCriticalScaleOn, dif_pos hx]

/- The paper interval bounds are automatic; they are not additional source
fields for continuum dyadic selection. -/
omit [MeasurableSpace X] in
theorem actualCriticalScaleOn_bounds
    (E : Set X) (family : X → Finset alpha)
    (distance : X → alpha → alpha → Real)
    {delta ceiling exponent : Real}
    (hfamily : ∀ x ∈ E, (family x).Nonempty)
    (hdeltaCeiling : delta ≤ ceiling)
    {x : X} (hx : x ∈ E) :
    delta ≤ actualCriticalScaleOn E family distance delta ceiling exponent
        hfamily x ∧
      actualCriticalScaleOn E family distance delta ceiling exponent
        hfamily x ≤ ceiling := by
  rw [actualCriticalScaleOn_eq E family distance delta ceiling exponent
    hfamily hx]
  exact finiteCriticalMaximizerScale_bounds (family x) (distance x)
    (hfamily x hx) hdeltaCeiling

/-- Once the real-valued actual critical scale is measurable, its literal
ceil-log dyadic label is automatically measurable. -/
theorem measurable_actualCriticalDyadicLabelOn
    (E : Set X) (family : X → Finset alpha)
    (distance : X → alpha → alpha → Real)
    (delta ceiling exponent : Real)
    (hfamily : ∀ x ∈ E, (family x).Nonempty)
    (hscale : Measurable
      (actualCriticalScaleOn E family distance delta ceiling exponent
        hfamily)) :
    Measurable (fun x => dyadicCeilBucket
      (actualCriticalScaleOn E family distance delta ceiling exponent
        hfamily x)) :=
  measurable_dyadicCeilBucket.comp hscale

#print axioms finiteCriticalMaximizerScale
#print axioms finiteCriticalMaximizerScale_bounds
#print axioms actualCriticalScaleOn
#print axioms actualCriticalScaleOn_eq
#print axioms actualCriticalScaleOn_bounds
#print axioms measurable_actualCriticalDyadicLabelOn

end

end FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
