import FamilyStickyCinematicL32FiniteNormCriticalBallV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteIncidenceNormCriticalBallV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1

noncomputable section

/-!
# Measurable finite-incidence labels for the local norm critical ball

The scale, centre, and literal ball are all evaluated from one finite active
incidence pattern.  Consequently every joint predicate involving these three
objects is measurable.  No arbitrary point-to-Finset map or selector is
assumed measurable.
-/

universe u v w

variable {X : Type u} {index : Type v} {alpha : Type w}
  [MeasurableSpace X]

/-- The selected norm scale attached to the same finite active pattern. -/
noncomputable def finiteIncidenceNormCriticalScaleValue
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (active : Finset index) : Real := by
  classical
  exact if hfamily : (familyOfActive active).Nonempty then
    finiteCriticalMaximizerScale (familyOfActive active)
      (distanceOfActive active) delta ceiling exponent hfamily
  else delta

/-- The local norm critical ball attached to one finite active pattern, with
the honest empty-family fallback. -/
noncomputable def finiteIncidenceNormCriticalBallValue
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (active : Finset index) : Finset alpha := by
  classical
  exact if hfamily : (familyOfActive active).Nonempty then
    finiteNormCriticalBall (familyOfActive active)
      (distanceOfActive active) delta ceiling exponent hfamily
  else ∅

/-- Pointwise local ball read only from the literal finite incidence pattern. -/
noncomputable def finiteIncidenceNormCriticalBall
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) : X → Finset alpha :=
  fun x => finiteIncidenceNormCriticalBallValue familyOfActive
    distanceOfActive delta ceiling exponent
    (finiteIncidenceActiveAtPoint ambient incidence x)

/-- On a nonempty active family the fallback disappears definitionally. -/
theorem finiteIncidenceNormCriticalBallValue_eq_of_nonempty
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (active : Finset index)
    (hfamily : (familyOfActive active).Nonempty) :
    finiteIncidenceNormCriticalBallValue familyOfActive distanceOfActive
        delta ceiling exponent active =
      finiteNormCriticalBall (familyOfActive active)
        (distanceOfActive active) delta ceiling exponent hfamily := by
  simp only [finiteIncidenceNormCriticalBallValue, dif_pos hfamily]

/-- Every joint predicate of the selected scale, centre, and local ball is
measurable because all three are functions of the same finite pattern. -/
theorem measurableSet_finiteIncidenceNormCriticalStatePredicate
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real)
    (accept : Real → Option alpha → Finset alpha → Prop) :
    MeasurableSet {x |
      accept
        (finiteIncidenceNormCriticalScaleValue familyOfActive distanceOfActive
          delta ceiling exponent
          (finiteIncidenceActiveAtPoint ambient incidence x))
        (finiteIncidenceCriticalCenterValue familyOfActive distanceOfActive
          delta ceiling exponent
          (finiteIncidenceActiveAtPoint ambient incidence x))
        (finiteIncidenceNormCriticalBall ambient incidence familyOfActive
          distanceOfActive delta ceiling exponent x)} := by
  simpa only [finiteIncidenceNormCriticalBall] using
    (measurableSet_finiteIncidencePatternPredicate ambient incidence
      hincidence (fun active =>
        accept
          (finiteIncidenceNormCriticalScaleValue familyOfActive distanceOfActive
            delta ceiling exponent active)
          (finiteIncidenceCriticalCenterValue familyOfActive distanceOfActive
            delta ceiling exponent active)
          (finiteIncidenceNormCriticalBallValue familyOfActive
            distanceOfActive delta ceiling exponent active)))

/-- Membership of any fixed family member in the pointwise critical ball is
a measurable event. -/
theorem measurableSet_mem_finiteIncidenceNormCriticalBall
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) (f : alpha) :
    MeasurableSet {x |
      f ∈ finiteIncidenceNormCriticalBall ambient incidence familyOfActive
        distanceOfActive delta ceiling exponent x} := by
  simpa using
    (measurableSet_finiteIncidenceNormCriticalStatePredicate ambient incidence
      hincidence familyOfActive distanceOfActive delta ceiling exponent
      (fun _ _ ball => f ∈ ball))

/-- The pointwise critical-ball cardinal is a measurable natural-valued
label, again with no measurable-Finset assumption. -/
theorem measurable_finiteIncidenceNormCriticalBall_card
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real) :
    Measurable (fun x =>
      (finiteIncidenceNormCriticalBall ambient incidence familyOfActive
        distanceOfActive delta ceiling exponent x).card) := by
  change Measurable (fun x =>
    (finiteIncidenceNormCriticalBallValue familyOfActive distanceOfActive
      delta ceiling exponent
      (finiteIncidenceActiveAtPoint ambient incidence x)).card)
  exact measurable_finiteIncidencePatternValue ambient incidence hincidence
    (fun active =>
      (finiteIncidenceNormCriticalBallValue familyOfActive distanceOfActive
        delta ceiling exponent active).card)

#print axioms finiteIncidenceNormCriticalBallValue
#print axioms finiteIncidenceNormCriticalBall
#print axioms finiteIncidenceNormCriticalBallValue_eq_of_nonempty
#print axioms measurableSet_finiteIncidenceNormCriticalStatePredicate
#print axioms measurableSet_mem_finiteIncidenceNormCriticalBall
#print axioms measurable_finiteIncidenceNormCriticalBall_card

end

end FamilyStickyCinematicL32FiniteIncidenceNormCriticalBallV1
