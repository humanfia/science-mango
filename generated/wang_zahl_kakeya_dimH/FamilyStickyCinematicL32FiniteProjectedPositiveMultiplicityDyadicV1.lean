import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
import FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

universe u v

/-! # Positive dyadic cardinality cells for any finite projected shading -/

def projectedActiveMultiplicity
    {point : Type u} [MeasurableSpace point] {index : Type v}
    (Z : FiniteProjectedShading point index) (x : point) : Real :=
  (Z.activeAtPoint x).card

theorem measurable_projectedActiveMultiplicity
    {point : Type u} [MeasurableSpace point] {index : Type v}
    (Z : FiniteProjectedShading point index) :
    Measurable (projectedActiveMultiplicity Z) := by
  exact Z.measurable_activeValue fun active => (active.card : Real)

def projectedPositiveMultiplicityDyadicCell
    {point : Type u} [MeasurableSpace point] {index : Type v}
    (Z : FiniteProjectedShading point index) (label : Int) : Set point :=
  continuumCriticalSingleDyadicCell Z.base
    (projectedActiveMultiplicity Z) label

theorem exists_projectedPositiveMultiplicityDyadicCell
    {point : Type u} [MeasurableSpace point] {index : Type v}
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (hbaseNonempty : Z.base.Nonempty)
    (hactive : ∀ x, x ∈ Z.base → (Z.activeAtPoint x).Nonempty) :
    ∃ label ∈ Finset.Icc (dyadicCeilBucket 1)
        (dyadicCeilBucket (Z.ambient.card : Real)),
      mu Z.base /
          (continuumCriticalSingleDyadicBinFactor 1
            (Z.ambient.card : Real) : ENNReal) ≤
        mu (projectedPositiveMultiplicityDyadicCell Z label) ∧
      0 < dyadicCeilUpper label ∧
      MeasurableSet (projectedPositiveMultiplicityDyadicCell Z label) ∧
      projectedPositiveMultiplicityDyadicCell Z label ⊆ Z.base ∧
      ∀ x ∈ projectedPositiveMultiplicityDyadicCell Z label,
        dyadicCeilUpper label / 2 < projectedActiveMultiplicity Z x ∧
          projectedActiveMultiplicity Z x ≤ dyadicCeilUpper label := by
  obtain ⟨x0, hx0⟩ := hbaseNonempty
  have hambientCard : (1 : Real) ≤ Z.ambient.card := by
    have hcard : 1 ≤ (Z.activeAtPoint x0).card :=
      Finset.one_le_card.mpr (hactive x0 hx0)
    exact_mod_cast hcard.trans (Finset.card_le_card
      (finiteIncidenceActiveAtPoint_subset Z.ambient
        (fun i x => x ∈ Z.carrier i) x0))
  have hscaleBounds : ∀ x ∈ Z.base,
      (1 : Real) ≤ projectedActiveMultiplicity Z x ∧
        projectedActiveMultiplicity Z x ≤ Z.ambient.card := by
    intro x hx
    constructor
    · change (1 : Real) ≤ ((Z.activeAtPoint x).card : Real)
      exact_mod_cast Finset.one_le_card.mpr (hactive x hx)
    · change ((Z.activeAtPoint x).card : Real) ≤ (Z.ambient.card : Real)
      exact_mod_cast Finset.card_le_card
        (finiteIncidenceActiveAtPoint_subset Z.ambient
          (fun i x => x ∈ Z.carrier i) x)
  obtain ⟨label, hlabel, hmeasure, hlabelPos, hbin⟩ :=
    exists_continuumCritical_single_dyadic_selection mu
      (projectedActiveMultiplicity Z) Z.measurable_base (by norm_num)
      hambientCard (measurable_projectedActiveMultiplicity Z) hscaleBounds
  refine ⟨label, hlabel, ?_, hlabelPos, ?_, ?_, hbin⟩
  · simpa [projectedPositiveMultiplicityDyadicCell] using hmeasure
  · exact measurableSet_continuumCriticalSingleDyadicCell
      Z.measurable_base (measurable_projectedActiveMultiplicity Z) label
  · intro x hx
    exact hx.1

#print axioms projectedActiveMultiplicity
#print axioms measurable_projectedActiveMultiplicity
#print axioms projectedPositiveMultiplicityDyadicCell
#print axioms exists_projectedPositiveMultiplicityDyadicCell

end

end FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
