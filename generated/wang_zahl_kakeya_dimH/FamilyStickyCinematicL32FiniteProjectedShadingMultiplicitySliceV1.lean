import FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1

noncomputable section

/-!
# Finite projected shadings and their honest multiplicity slices

The existing three-dimensional `Shading` API cannot itself serve as the PYZ
set `E₂`: the latter lives in the two-dimensional twisted-projection plane,
and a measurable image theorem for arbitrary shaded carriers is absent.  The
first data lost by the current cinematic API are therefore the finite family
of *projected* measurable carrier events.

This structure is the minimal faithful strengthening.  It stores the base
set and each projected carrier, together with their source measurability.  It
does not store a multiplicity slice, an active map, or any desired critical
scale conclusion; all of those are defined and proved below.
-/

universe u v

variable {point : Type u} {index : Type v} [MeasurableSpace point]

/-- A finite family of measurable projected shading events inside one
measurable source set. -/
structure FiniteProjectedShading (point : Type u) (index : Type v)
    [MeasurableSpace point] where
  ambient : Finset index
  base : Set point
  carrier : index → Set point
  measurable_base : MeasurableSet base
  measurable_carrier : ∀ i ∈ ambient, MeasurableSet (carrier i)

/-- Literal active projected shadings through a point. -/
noncomputable def FiniteProjectedShading.activeAtPoint
    (Z : FiniteProjectedShading point index) : point → Finset index :=
  finiteIncidenceActiveAtPoint Z.ambient (fun i x => x ∈ Z.carrier i)

@[simp] theorem FiniteProjectedShading.mem_activeAtPoint
    (Z : FiniteProjectedShading point index) (x : point) (i : index) :
    i ∈ Z.activeAtPoint x ↔ i ∈ Z.ambient ∧ x ∈ Z.carrier i := by
  exact mem_finiteIncidenceActiveAtPoint Z.ambient
    (fun i x => x ∈ Z.carrier i) x i

/-- Predicate selecting one finite multiplicity band. -/
def multiplicityBandAccept (lower upper : Nat) (active : Finset index) : Prop :=
  lower ≤ active.card ∧ active.card ≤ upper

/-- The actual projected source slice used for one double-dyadic run. -/
def FiniteProjectedShading.multiplicityBand
    (Z : FiniteProjectedShading point index) (lower upper : Nat) : Set point :=
  finiteIncidencePatternSlice Z.base Z.ambient
    (fun i x => x ∈ Z.carrier i) (multiplicityBandAccept lower upper)

theorem FiniteProjectedShading.mem_multiplicityBand
    (Z : FiniteProjectedShading point index)
    {lower upper : Nat} {x : point} :
    x ∈ Z.multiplicityBand lower upper ↔
      x ∈ Z.base ∧ lower ≤ (Z.activeAtPoint x).card ∧
        (Z.activeAtPoint x).card ≤ upper := by
  rfl

/-- Every projected multiplicity band is measurable, generated solely from
the actual finite carrier events. -/
theorem FiniteProjectedShading.measurableSet_multiplicityBand
    (Z : FiniteProjectedShading point index) (lower upper : Nat) :
    MeasurableSet (Z.multiplicityBand lower upper) := by
  exact measurableSet_finiteIncidencePatternSlice Z.ambient
    (fun i x => x ∈ Z.carrier i) (multiplicityBandAccept lower upper)
    Z.measurable_base (fun i hi => Z.measurable_carrier i hi)

/-- Every value computed from the active projected shading pattern is
measurable. -/
theorem FiniteProjectedShading.measurable_activeValue
    {target : Type*} [MeasurableSpace target]
    (Z : FiniteProjectedShading point index)
    (value : Finset index → target) :
    Measurable (fun x => value (Z.activeAtPoint x)) := by
  exact measurable_finiteIncidencePatternValue Z.ambient
    (fun i x => x ∈ Z.carrier i)
    (fun i hi => Z.measurable_carrier i hi) value

#print axioms FiniteProjectedShading
#print axioms FiniteProjectedShading.activeAtPoint
#print axioms FiniteProjectedShading.mem_activeAtPoint
#print axioms FiniteProjectedShading.multiplicityBand
#print axioms FiniteProjectedShading.mem_multiplicityBand
#print axioms FiniteProjectedShading.measurableSet_multiplicityBand
#print axioms FiniteProjectedShading.measurable_activeValue

end


end FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
