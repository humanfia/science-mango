import FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

/-!
# Post-norm-cover `Y₁` and `E₂`

The measurable carriers are the literal localized tangency carriers from the
preceding module.  Packaging them as a finite projected shading makes every
multiplicity band `E₂` a definitionally generated measurable set.  Neither
the active map nor measurability of `E₂` is supplied as a premise.
-/

universe u v w

variable {X : Type u} {index : Type v} {alpha : Type w}
  [MeasurableSpace X]

/-- The actual finite projected `Y₁` family after norm localization. -/
noncomputable def finiteIncidenceLocalizedTangencyY1
    (base : Set X) (hbase : MeasurableSet base)
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (elementOfIndex : index → alpha)
    (delta ceiling exponent threshold : Real) :
    FiniteProjectedShading X index where
  ambient := ambient
  base := base
  carrier := finiteIncidenceLocalizedTangencyCarrier ambient incidence
    familyOfActive normDistance globalScale globalCenter tangencyDistance
    elementOfIndex delta ceiling exponent threshold
  measurable_base := hbase
  measurable_carrier := by
    intro i _hi
    exact measurableSet_finiteIncidenceLocalizedTangencyCarrier ambient
      incidence hincidence familyOfActive normDistance globalScale
      globalCenter tangencyDistance elementOfIndex delta ceiling exponent
      threshold i

/-- The `Y₁` active family is definitionally the finite filter by the
localized tangency carriers. -/
theorem activeAtPoint_finiteIncidenceLocalizedTangencyY1
    (base : Set X) (hbase : MeasurableSet base)
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (elementOfIndex : index → alpha)
    (delta ceiling exponent threshold : Real) (x : X) :
    FiniteProjectedShading.activeAtPoint
      (finiteIncidenceLocalizedTangencyY1 base hbase ambient incidence
        hincidence familyOfActive normDistance globalScale globalCenter
        tangencyDistance elementOfIndex delta ceiling exponent threshold) x =
      finiteIncidenceActiveAtPoint ambient
        (fun i x => x ∈ finiteIncidenceLocalizedTangencyCarrier ambient
          incidence familyOfActive normDistance globalScale globalCenter
          tangencyDistance elementOfIndex delta ceiling exponent threshold i)
        x :=
  rfl

/-- The literal post-cover `E₂` multiplicity band. -/
def finiteIncidenceLocalizedTangencyE2
    (base : Set X) (hbase : MeasurableSet base)
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (elementOfIndex : index → alpha)
    (delta ceiling exponent threshold : Real)
    (lower upper : Nat) : Set X :=
  (finiteIncidenceLocalizedTangencyY1 base hbase ambient incidence hincidence
    familyOfActive normDistance globalScale globalCenter tangencyDistance
    elementOfIndex delta ceiling exponent threshold).multiplicityBand
      lower upper

/-- `E₂` is measurable by finite incidence, not by an arbitrary-set input. -/
theorem measurableSet_finiteIncidenceLocalizedTangencyE2
    (base : Set X) (hbase : MeasurableSet base)
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (elementOfIndex : index → alpha)
    (delta ceiling exponent threshold : Real)
    (lower upper : Nat) :
    MeasurableSet (finiteIncidenceLocalizedTangencyE2 base hbase ambient
      incidence hincidence familyOfActive normDistance globalScale
      globalCenter tangencyDistance elementOfIndex delta ceiling exponent
      threshold lower upper) := by
  exact FiniteProjectedShading.measurableSet_multiplicityBand
    (finiteIncidenceLocalizedTangencyY1 base hbase ambient incidence
      hincidence familyOfActive normDistance globalScale globalCenter
      tangencyDistance elementOfIndex delta ceiling exponent threshold)
    lower upper

#print axioms finiteIncidenceLocalizedTangencyY1
#print axioms activeAtPoint_finiteIncidenceLocalizedTangencyY1
#print axioms finiteIncidenceLocalizedTangencyE2
#print axioms measurableSet_finiteIncidenceLocalizedTangencyE2

end

end FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1
