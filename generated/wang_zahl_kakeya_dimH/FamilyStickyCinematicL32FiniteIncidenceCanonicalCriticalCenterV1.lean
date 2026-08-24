import FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
import FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32Lemma57CanonicalMaximizerV1
open FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1

noncomputable section

/-!
# Canonical critical centres from finite measurable incidence patterns

The PYZ centre k_x is chosen by the same finite maximizer that chooses its
critical scale.  We expose the centre as an Option-valued function of the
literal finite incidence pattern.  Its fibres, and every predicate involving
it and that pattern, are measurable without postulating measurability of an
arbitrary pointwise selector.
-/

universe u v w

variable {X : Type u} {index : Type v} {alpha : Type w}
  [MeasurableSpace X]

/-- The centre component paired with finiteCriticalMaximizerScale. -/
noncomputable def finiteCriticalMaximizerCenter
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (delta ceiling exponent : Real) (hfamily : family.Nonempty) : alpha :=
  (canonicalMaximizerData family
    (finiteCriticalScaleCarrier family distance delta ceiling)
    distance exponent
    (finiteCriticalScaleCarrier_nonempty family distance delta ceiling)
    hfamily).center

theorem finiteCriticalMaximizerCenter_mem
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (delta ceiling exponent : Real) (hfamily : family.Nonempty) :
    finiteCriticalMaximizerCenter family distance delta ceiling exponent
      hfamily ∈ family :=
  (canonicalMaximizerData family
    (finiteCriticalScaleCarrier family distance delta ceiling)
    distance exponent
    (finiteCriticalScaleCarrier_nonempty family distance delta ceiling)
    hfamily).center_mem

/-- Honest total selector on incidence patterns.  Empty families map to none. -/
noncomputable def finiteIncidenceCriticalCenterValue
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (active : Finset index) :
    Option alpha := by
  classical
  exact if hfamily : (familyOfActive active).Nonempty then
    some (finiteCriticalMaximizerCenter (familyOfActive active)
      (distanceOfActive active) delta ceiling exponent hfamily)
  else none

/-- The canonical centre selected from the literal active-incidence pattern. -/
noncomputable def finiteIncidenceCriticalCenter
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) : X → Option alpha :=
  fun x => finiteIncidenceCriticalCenterValue familyOfActive
    distanceOfActive delta ceiling exponent
    (finiteIncidenceActiveAtPoint ambient incidence x)

theorem finiteIncidenceCriticalCenterValue_eq_some_of_nonempty
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (active : Finset index)
    (hfamily : (familyOfActive active).Nonempty) :
    finiteIncidenceCriticalCenterValue familyOfActive distanceOfActive
        delta ceiling exponent active =
      some (finiteCriticalMaximizerCenter (familyOfActive active)
        (distanceOfActive active) delta ceiling exponent hfamily) := by
  simp only [finiteIncidenceCriticalCenterValue, dif_pos hfamily]

omit [MeasurableSpace X] in
theorem finiteIncidenceCriticalCenter_exists_mem_of_nonempty
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (x : X)
    (hfamily : (familyOfActive
      (finiteIncidenceActiveAtPoint ambient incidence x)).Nonempty) :
    ∃ center,
      finiteIncidenceCriticalCenter ambient incidence familyOfActive
          distanceOfActive delta ceiling exponent x = some center ∧
        center ∈ familyOfActive
          (finiteIncidenceActiveAtPoint ambient incidence x) := by
  refine ⟨finiteCriticalMaximizerCenter
      (familyOfActive (finiteIncidenceActiveAtPoint ambient incidence x))
      (distanceOfActive (finiteIncidenceActiveAtPoint ambient incidence x))
      delta ceiling exponent hfamily, ?_, ?_⟩
  · exact finiteIncidenceCriticalCenterValue_eq_some_of_nonempty
      familyOfActive distanceOfActive delta ceiling exponent
      (finiteIncidenceActiveAtPoint ambient incidence x) hfamily
  · exact finiteCriticalMaximizerCenter_mem
      (familyOfActive (finiteIncidenceActiveAtPoint ambient incidence x))
      (distanceOfActive (finiteIncidenceActiveAtPoint ambient incidence x))
      delta ceiling exponent hfamily

/-- Every event computed from the incidence pattern and its canonical centre
is measurable.  This is the finite-selector measurability theorem used for
the projected Y_1(f) carriers. -/
theorem measurableSet_finiteIncidenceCriticalCenterPredicate
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real)
    (accept : Finset index → Option alpha → Prop) :
    MeasurableSet {x |
      accept (finiteIncidenceActiveAtPoint ambient incidence x)
        (finiteIncidenceCriticalCenter ambient incidence familyOfActive
          distanceOfActive delta ceiling exponent x)} := by
  simpa only [finiteIncidenceCriticalCenter] using
    (measurableSet_finiteIncidencePatternPredicate ambient incidence
      hincidence (fun active => accept active
        (finiteIncidenceCriticalCenterValue familyOfActive distanceOfActive
          delta ceiling exponent active)))

/-- In particular, every fixed centre fibre is measurable, without placing
a measurable-space structure on alpha. -/
theorem measurableSet_finiteIncidenceCriticalCenter_eq
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (center : Option alpha) :
    MeasurableSet {x |
      finiteIncidenceCriticalCenter ambient incidence familyOfActive
        distanceOfActive delta ceiling exponent x = center} := by
  simpa using
    (measurableSet_finiteIncidenceCriticalCenterPredicate
      ambient incidence hincidence familyOfActive distanceOfActive
      delta ceiling exponent (fun _ selected => selected = center))

#print axioms finiteCriticalMaximizerCenter
#print axioms finiteCriticalMaximizerCenter_mem
#print axioms finiteIncidenceCriticalCenter
#print axioms finiteIncidenceCriticalCenter_exists_mem_of_nonempty
#print axioms measurableSet_finiteIncidenceCriticalCenterPredicate
#print axioms measurableSet_finiteIncidenceCriticalCenter_eq

end

end FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
