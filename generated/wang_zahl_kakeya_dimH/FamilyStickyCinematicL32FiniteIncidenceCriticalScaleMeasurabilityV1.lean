import FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
import FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1

noncomputable section

/-!
# Critical scales from finite measurable incidence patterns

The finite critical maximizer need not be analyzed as a real-valued formula.
Once its finite family and distance table are determined by one finite
incidence pattern, it is simply a function on a finite discrete state space.
This module therefore derives measurability of the actual critical scale from
literal measurable incidence events, without assuming measurability of an
arbitrary `point → Finset` map.
-/

universe u v w

variable {X : Type u} {index : Type v} {alpha : Type w}
  [MeasurableSpace X]

/-- A total critical-scale value attached to a finite incidence pattern.  The
fallback value is used only for patterns whose associated family is empty. -/
noncomputable def finiteIncidenceCriticalScaleValue
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (active : Finset index) : Real := by
  classical
  exact if hfamily : (familyOfActive active).Nonempty then
    finiteCriticalMaximizerScale (familyOfActive active)
      (distanceOfActive active) delta ceiling exponent hfamily
  else delta

/-- The total critical scale read from the literal active-incidence pattern. -/
noncomputable def finiteIncidenceCriticalScale
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) : X → Real :=
  fun x => finiteIncidenceCriticalScaleValue familyOfActive distanceOfActive
    delta ceiling exponent
    (finiteIncidenceActiveAtPoint ambient incidence x)

/-- A critical scale depending on a finite measurable incidence pattern is
measurable, including its honest empty-family fallback. -/
theorem measurable_finiteIncidenceCriticalScale
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient,
      MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) :
    Measurable (finiteIncidenceCriticalScale ambient incidence familyOfActive
      distanceOfActive delta ceiling exponent) := by
  exact measurable_finiteIncidencePatternValue ambient incidence hincidence
    (finiteIncidenceCriticalScaleValue familyOfActive distanceOfActive
      delta ceiling exponent)

/-- On a measurable source set where the incidence-determined family is
nonempty, the actual finite critical-maximizer scale is automatically
measurable.  No measurability hypothesis on `activeAtPoint`, `family`, or the
finite distance tables is required. -/
theorem measurable_actualCriticalScaleOn_of_finiteIncidence
    (E : Set X) (hE : MeasurableSet E)
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient,
      MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real)
    (hfamily : ∀ x ∈ E,
      (familyOfActive
        (finiteIncidenceActiveAtPoint ambient incidence x)).Nonempty) :
    Measurable
      (actualCriticalScaleOn E
        (fun x => familyOfActive
          (finiteIncidenceActiveAtPoint ambient incidence x))
        (fun x => distanceOfActive
          (finiteIncidenceActiveAtPoint ambient incidence x))
        delta ceiling exponent hfamily) := by
  classical
  have hraw : Measurable
      (finiteIncidenceCriticalScale ambient incidence familyOfActive
        distanceOfActive delta ceiling exponent) :=
    measurable_finiteIncidenceCriticalScale ambient incidence hincidence
      familyOfActive distanceOfActive delta ceiling exponent
  let hdecidable : DecidablePred (fun x : X => x ∈ E) :=
    fun x => Classical.propDecidable (x ∈ E)
  have hpiecewise : Measurable (fun x =>
      if x ∈ E then
        finiteIncidenceCriticalScale ambient incidence familyOfActive
          distanceOfActive delta ceiling exponent x
      else delta) :=
    @Measurable.ite X Real _ _ _ _ (fun x => x ∈ E) hdecidable
      hE hraw measurable_const
  have heq :
      actualCriticalScaleOn E
          (fun x => familyOfActive
            (finiteIncidenceActiveAtPoint ambient incidence x))
          (fun x => distanceOfActive
            (finiteIncidenceActiveAtPoint ambient incidence x))
          delta ceiling exponent hfamily =
        (fun x => if x ∈ E then
          finiteIncidenceCriticalScale ambient incidence familyOfActive
            distanceOfActive delta ceiling exponent x
          else delta) := by
    funext x
    by_cases hx : x ∈ E
    · simp only [actualCriticalScaleOn, dif_pos hx, if_pos hx,
        finiteIncidenceCriticalScale, finiteIncidenceCriticalScaleValue]
      rw [dif_pos (hfamily x hx)]
    · simp only [actualCriticalScaleOn, dif_neg hx, if_neg hx]
  rw [heq]
  exact hpiecewise

#print axioms finiteIncidenceCriticalScaleValue
#print axioms finiteIncidenceCriticalScale
#print axioms measurable_finiteIncidenceCriticalScale
#print axioms measurable_actualCriticalScaleOn_of_finiteIncidence

end

end FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
