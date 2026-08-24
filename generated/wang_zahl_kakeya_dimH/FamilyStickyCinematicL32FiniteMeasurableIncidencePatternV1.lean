import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-!
# Finite measurable incidence patterns

An actual pointwise active family is obtained by filtering one fixed finite
ambient family by geometric incidence events.  If each event is measurable,
then every function of the resulting finite incidence pattern is measurable.
This is stronger and more faithful than assuming an arbitrary
`point → Finset index` map to be measurable.
-/

universe u v w

variable {X : Type u} {index : Type v} [MeasurableSpace X]

/-- The active indices at a point, cut out from one fixed finite ambient set
by literal incidence predicates. -/
noncomputable def finiteIncidenceActiveAtPoint
    (ambient : Finset index) (incidence : index → X → Prop) :
    X → Finset index := by
  classical
  exact fun x => ambient.filter fun i => incidence i x

omit [MeasurableSpace X] in
@[simp] theorem mem_finiteIncidenceActiveAtPoint
    (ambient : Finset index) (incidence : index → X → Prop)
    (x : X) (i : index) :
    i ∈ finiteIncidenceActiveAtPoint ambient incidence x ↔
      i ∈ ambient ∧ incidence i x := by
  classical
  simp [finiteIncidenceActiveAtPoint]

omit [MeasurableSpace X] in
theorem finiteIncidenceActiveAtPoint_subset
    (ambient : Finset index) (incidence : index → X → Prop) (x : X) :
    finiteIncidenceActiveAtPoint ambient incidence x ⊆ ambient := by
  classical
  exact Finset.filter_subset _ _

/-- Every value computed solely from a finite measurable incidence pattern is
measurable.  The target can be arbitrary; no countability or measurable
structure on the index type is required. -/
theorem measurable_finiteIncidencePatternValue
    {target : Type w} [MeasurableSpace target]
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient,
      MeasurableSet {x | incidence i x})
    (value : Finset index → target) :
    Measurable (fun x =>
      value (finiteIncidenceActiveAtPoint ambient incidence x)) := by
  classical
  induction ambient using Finset.induction_on generalizing value with
  | empty =>
      change Measurable (fun _ : X => value ∅)
      exact measurable_const
  | @insert a s ha ih =>
      have haMeasurable : MeasurableSet {x | incidence a x} :=
        hincidence a (by simp)
      have hsMeasurable : ∀ i ∈ s,
          MeasurableSet {x | incidence i x} := by
        intro i hi
        exact hincidence i (by simp [hi])
      have htrue : Measurable (fun x =>
          value (insert a
            (finiteIncidenceActiveAtPoint s incidence x))) :=
        ih hsMeasurable (fun active => value (insert a active))
      have hfalse : Measurable (fun x =>
          value (finiteIncidenceActiveAtPoint s incidence x)) :=
        ih hsMeasurable value
      let hdecidable : DecidablePred (incidence a) :=
        fun x => Classical.propDecidable (incidence a x)
      have hite : Measurable (fun x =>
          if incidence a x then
            value (insert a
              (finiteIncidenceActiveAtPoint s incidence x))
          else value (finiteIncidenceActiveAtPoint s incidence x)) :=
        @Measurable.ite X target _ _ _ _ (incidence a) hdecidable
          haMeasurable htrue hfalse
      have heq : (fun x =>
          value (finiteIncidenceActiveAtPoint (insert a s) incidence x)) =
          (fun x => if incidence a x then
            value (insert a
              (finiteIncidenceActiveAtPoint s incidence x))
            else value
              (finiteIncidenceActiveAtPoint s incidence x)) := by
        funext x
        by_cases hx : incidence a x <;>
          simp [finiteIncidenceActiveAtPoint, Finset.filter_insert, hx]
      rw [heq]
      exact hite

/-- Any predicate on the finite incidence pattern cuts out a measurable set.
In particular this covers cardinality, popularity, coefficient-bucket, and
finite conjunction/disjunction restrictions. -/
theorem measurableSet_finiteIncidencePatternPredicate
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient,
      MeasurableSet {x | incidence i x})
    (accept : Finset index → Prop) :
    MeasurableSet {x |
      accept (finiteIncidenceActiveAtPoint ambient incidence x)} := by
  classical
  let flag : Finset index → Bool := fun active => decide (accept active)
  have hflag : Measurable (fun x =>
      flag (finiteIncidenceActiveAtPoint ambient incidence x)) :=
    measurable_finiteIncidencePatternValue ambient incidence hincidence flag
  have hpreimage := hflag (measurableSet_singleton true)
  have heq :
      (fun x => flag
        (finiteIncidenceActiveAtPoint ambient incidence x)) ⁻¹' {true} =
        {x | accept
          (finiteIncidenceActiveAtPoint ambient incidence x)} := by
    ext x
    simp [flag]
  rw [heq] at hpreimage
  exact hpreimage

/-- A measurable base set restricted by any predicate of the finite incidence
pattern.  This is the minimal honest shape for a continuum `E₂` produced by
finite multiplicity/level pigeonholing. -/
def finiteIncidencePatternSlice
    (base : Set X) (ambient : Finset index)
    (incidence : index → X → Prop)
    (accept : Finset index → Prop) : Set X :=
  base ∩ {x | accept
    (finiteIncidenceActiveAtPoint ambient incidence x)}

theorem measurableSet_finiteIncidencePatternSlice
    {base : Set X} (ambient : Finset index)
    (incidence : index → X → Prop)
    (accept : Finset index → Prop)
    (hbase : MeasurableSet base)
    (hincidence : ∀ i ∈ ambient,
      MeasurableSet {x | incidence i x}) :
    MeasurableSet
      (finiteIncidencePatternSlice base ambient incidence accept) := by
  exact hbase.inter
    (measurableSet_finiteIncidencePatternPredicate ambient incidence
      hincidence accept)

#print axioms finiteIncidenceActiveAtPoint
#print axioms mem_finiteIncidenceActiveAtPoint
#print axioms finiteIncidenceActiveAtPoint_subset
#print axioms measurable_finiteIncidencePatternValue
#print axioms measurableSet_finiteIncidencePatternPredicate
#print axioms measurableSet_finiteIncidencePatternSlice

end

end FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
