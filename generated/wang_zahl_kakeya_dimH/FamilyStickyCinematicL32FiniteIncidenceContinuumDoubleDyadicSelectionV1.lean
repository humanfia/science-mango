import FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
import FamilyStickyCinematicL32ContinuumActualCriticalDoubleDyadicSelectionV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32FiniteIncidenceContinuumDoubleDyadicSelectionV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteIncidenceCriticalScaleMeasurabilityV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32ContinuumActualCriticalDoubleDyadicSelectionV1
open FamilyStickyCinematicL32ContinuumCriticalDoubleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# Continuum double-dyadic selection from literal finite incidences

This is the source-facing adapter.  Its continuum set is a measurable base
restricted by a predicate of one finite incidence pattern.  Both critical
families and both distance tables are functions of that same pattern.
Consequently measurability of the source set and of the two actual critical
scales is produced internally from the individual geometric incidence
events.
-/

universe u v w

variable {X : Type u} {index : Type v} {alpha : Type w}
  [MeasurableSpace X]

/-- The finite critical family obtained from the literal active incidences. -/
noncomputable def finiteIncidenceFamilyAt
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha) : X → Finset alpha :=
  fun x => familyOfActive
    (finiteIncidenceActiveAtPoint ambient incidence x)

/-- A finite distance table obtained from the literal active incidences. -/
noncomputable def finiteIncidenceDistanceAt
    (ambient : Finset index) (incidence : index → X → Prop)
    (distanceOfActive : Finset index → alpha → alpha → Real) :
    X → alpha → alpha → Real :=
  fun x => distanceOfActive
    (finiteIncidenceActiveAtPoint ambient incidence x)

/-- The actual critical scale on an incidence-pattern slice, extended by
`delta` off that slice. -/
noncomputable def finiteIncidenceActualCriticalScaleOnSlice
    (base : Set X) (ambient : Finset index)
    (incidence : index → X → Prop)
    (accept : Finset index → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (distanceOfActive : Finset index → alpha → alpha → Real)
    (delta ceiling exponent : Real)
    (hfamily : ∀ x ∈
      finiteIncidencePatternSlice base ambient incidence accept,
      (finiteIncidenceFamilyAt ambient incidence familyOfActive x).Nonempty) :
    X → Real :=
  actualCriticalScaleOn
    (finiteIncidencePatternSlice base ambient incidence accept)
    (finiteIncidenceFamilyAt ambient incidence familyOfActive)
    (finiteIncidenceDistanceAt ambient incidence distanceOfActive)
    delta ceiling exponent hfamily

/-- The actual continuum double-dyadic pigeonhole, with all three analytic
measurability inputs generated from finite pointwise incidence events. -/
theorem exists_finiteIncidence_actualCritical_doubleDyadicSelection
    (μ : Measure X) (base : Set X)
    (ambient : Finset index) (incidence : index → X → Prop)
    (accept : Finset index → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (normDistanceOfActive tangencyDistanceOfActive :
      Finset index → alpha → alpha → Real)
    (delta normCeiling tangencyCeiling normExponent tangencyExponent : Real)
    (hbase : MeasurableSet base)
    (hincidence : ∀ i ∈ ambient,
      MeasurableSet {x | incidence i x})
    (hdelta : 0 < delta)
    (hnormCeiling : delta ≤ normCeiling)
    (htangencyCeiling : delta ≤ tangencyCeiling)
    (hfamily : ∀ x ∈
      finiteIncidencePatternSlice base ambient incidence accept,
      (finiteIncidenceFamilyAt ambient incidence familyOfActive x).Nonempty) :
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket delta)
        (dyadicCeilBucket normCeiling),
      ∃ tangencyLabel ∈ Finset.Icc (dyadicCeilBucket delta)
          (dyadicCeilBucket tangencyCeiling),
        μ (finiteIncidencePatternSlice base ambient incidence accept) /
            (continuumCriticalDoubleDyadicBinFactor delta normCeiling
              tangencyCeiling : ENNReal) ≤
          μ (continuumCriticalDoubleDyadicCell
            (finiteIncidencePatternSlice base ambient incidence accept)
            (finiteIncidenceActualCriticalScaleOnSlice base ambient incidence
              accept familyOfActive normDistanceOfActive delta normCeiling
              normExponent hfamily)
            (finiteIncidenceActualCriticalScaleOnSlice base ambient incidence
              accept familyOfActive tangencyDistanceOfActive delta
              tangencyCeiling tangencyExponent hfamily)
            normLabel tangencyLabel) ∧
        0 < dyadicCeilUpper normLabel ∧
        0 < dyadicCeilUpper tangencyLabel ∧
        ∀ x ∈ continuumCriticalDoubleDyadicCell
            (finiteIncidencePatternSlice base ambient incidence accept)
            (finiteIncidenceActualCriticalScaleOnSlice base ambient incidence
              accept familyOfActive normDistanceOfActive delta normCeiling
              normExponent hfamily)
            (finiteIncidenceActualCriticalScaleOnSlice base ambient incidence
              accept familyOfActive tangencyDistanceOfActive delta
              tangencyCeiling tangencyExponent hfamily)
            normLabel tangencyLabel,
          dyadicCeilUpper normLabel / 2 <
              finiteIncidenceActualCriticalScaleOnSlice base ambient incidence
                accept familyOfActive normDistanceOfActive delta normCeiling
                normExponent hfamily x ∧
          finiteIncidenceActualCriticalScaleOnSlice base ambient incidence
              accept familyOfActive normDistanceOfActive delta normCeiling
              normExponent hfamily x ≤ dyadicCeilUpper normLabel ∧
          dyadicCeilUpper tangencyLabel / 2 <
              finiteIncidenceActualCriticalScaleOnSlice base ambient incidence
                accept familyOfActive tangencyDistanceOfActive delta
                tangencyCeiling tangencyExponent hfamily x ∧
          finiteIncidenceActualCriticalScaleOnSlice base ambient incidence
              accept familyOfActive tangencyDistanceOfActive delta
              tangencyCeiling tangencyExponent hfamily x ≤
            dyadicCeilUpper tangencyLabel := by
  have hE : MeasurableSet
      (finiteIncidencePatternSlice base ambient incidence accept) :=
    measurableSet_finiteIncidencePatternSlice ambient incidence accept
      hbase hincidence
  have hnorm : Measurable
      (finiteIncidenceActualCriticalScaleOnSlice base ambient incidence accept
        familyOfActive normDistanceOfActive delta normCeiling normExponent
        hfamily) := by
    change Measurable
      (actualCriticalScaleOn
        (finiteIncidencePatternSlice base ambient incidence accept)
        (fun x => familyOfActive
          (finiteIncidenceActiveAtPoint ambient incidence x))
        (fun x => normDistanceOfActive
          (finiteIncidenceActiveAtPoint ambient incidence x))
        delta normCeiling normExponent hfamily)
    exact measurable_actualCriticalScaleOn_of_finiteIncidence
      (finiteIncidencePatternSlice base ambient incidence accept) hE
      ambient incidence hincidence familyOfActive normDistanceOfActive
      delta normCeiling normExponent hfamily
  have htangency : Measurable
      (finiteIncidenceActualCriticalScaleOnSlice base ambient incidence accept
        familyOfActive tangencyDistanceOfActive delta tangencyCeiling
        tangencyExponent hfamily) := by
    change Measurable
      (actualCriticalScaleOn
        (finiteIncidencePatternSlice base ambient incidence accept)
        (fun x => familyOfActive
          (finiteIncidenceActiveAtPoint ambient incidence x))
        (fun x => tangencyDistanceOfActive
          (finiteIncidenceActiveAtPoint ambient incidence x))
        delta tangencyCeiling tangencyExponent hfamily)
    exact measurable_actualCriticalScaleOn_of_finiteIncidence
      (finiteIncidencePatternSlice base ambient incidence accept) hE
      ambient incidence hincidence familyOfActive tangencyDistanceOfActive
      delta tangencyCeiling tangencyExponent hfamily
  simpa only [finiteIncidenceActualCriticalScaleOnSlice,
    finiteIncidenceFamilyAt, finiteIncidenceDistanceAt] using
    (exists_actualCritical_continuum_double_dyadic_selection μ
      (finiteIncidencePatternSlice base ambient incidence accept)
      (finiteIncidenceFamilyAt ambient incidence familyOfActive)
      (finiteIncidenceDistanceAt ambient incidence normDistanceOfActive)
      (finiteIncidenceDistanceAt ambient incidence tangencyDistanceOfActive)
      delta normCeiling tangencyCeiling normExponent tangencyExponent
      hE hdelta hnormCeiling htangencyCeiling hfamily hnorm htangency)

#print axioms finiteIncidenceFamilyAt
#print axioms finiteIncidenceDistanceAt
#print axioms finiteIncidenceActualCriticalScaleOnSlice
#print axioms exists_finiteIncidence_actualCritical_doubleDyadicSelection

end

end FamilyStickyCinematicL32FiniteIncidenceContinuumDoubleDyadicSelectionV1
