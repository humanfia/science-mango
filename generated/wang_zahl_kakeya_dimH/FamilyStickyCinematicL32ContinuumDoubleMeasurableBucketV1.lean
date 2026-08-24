import FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32ContinuumDoubleMeasurableBucketV1

open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1

noncomputable section

/-!
# Simultaneous measurable pigeonholing for two finite labels

This layer records the exact product loss for two continuum labels.  It uses
the product label itself, so the selected set is one literal intersection of
the two cells and no finite approximation to the source set is introduced.
-/

universe u v w

variable {X : Type u} {labelType₁ : Type v} {labelType₂ : Type w}
  [MeasurableSpace X]
  [MeasurableSpace labelType₁] [MeasurableSingletonClass labelType₁]
  [MeasurableSpace labelType₂] [MeasurableSingletonClass labelType₂]

/-- The simultaneous cell for two labels. -/
def measurableDoubleLabelCell (E : Set X)
    (label₁ : X → labelType₁) (label₂ : X → labelType₂)
    (b₁ : labelType₁) (b₂ : labelType₂) : Set X :=
  measurableLabelCell E (fun x => (label₁ x, label₂ x)) (b₁, b₂)

theorem measurableSet_measurableDoubleLabelCell
    {E : Set X} {label₁ : X → labelType₁} {label₂ : X → labelType₂}
    (hE : MeasurableSet E) (hlabel₁ : Measurable label₁)
    (hlabel₂ : Measurable label₂) (b₁ : labelType₁) (b₂ : labelType₂) :
    MeasurableSet (measurableDoubleLabelCell E label₁ label₂ b₁ b₂) := by
  have hpair : Measurable (fun x => (label₁ x, label₂ x)) :=
    Measurable.prod hlabel₁ hlabel₂
  simpa [measurableDoubleLabelCell, measurableLabelCell] using
    measurableSet_measurableLabelCell hE hpair (b₁, b₂)

/-- Two finite measurable labels retain a simultaneous cell of at least the
average measure, with exact product denominator. -/
theorem exists_measurableDoubleLabelCell_measure_ge_average
    (μ : Measure X) {E : Set X}
    {label₁ : X → labelType₁} {label₂ : X → labelType₂}
    (labels₁ : Finset labelType₁) (labels₂ : Finset labelType₂)
    (hlabels₁ : labels₁.Nonempty) (hlabels₂ : labels₂.Nonempty)
    (hE : MeasurableSet E) (hlabel₁ : Measurable label₁)
    (hlabel₂ : Measurable label₂)
    (hrange₁ : ∀ x ∈ E, label₁ x ∈ labels₁)
    (hrange₂ : ∀ x ∈ E, label₂ x ∈ labels₂) :
    ∃ b₁ ∈ labels₁, ∃ b₂ ∈ labels₂,
      μ E / ((labels₁.card * labels₂.card : Nat) : ENNReal) ≤
        μ (measurableDoubleLabelCell E label₁ label₂ b₁ b₂) := by
  classical
  rcases hlabels₁ with ⟨witness₁, hwitness₁⟩
  rcases hlabels₂ with ⟨witness₂, hwitness₂⟩
  have hproduct : (labels₁.product labels₂).Nonempty :=
    ⟨(witness₁, witness₂), Finset.mem_product.mpr
      ⟨hwitness₁, hwitness₂⟩⟩
  have hpair : Measurable (fun x => (label₁ x, label₂ x)) :=
    Measurable.prod hlabel₁ hlabel₂
  obtain ⟨b, hb, hmeasure⟩ :=
    exists_measurableLabelCell_measure_ge_average μ
      (labels₁.product labels₂) hproduct hE hpair
      (fun x hx => Finset.mem_product.mpr
        ⟨hrange₁ x hx, hrange₂ x hx⟩)
  rcases b with ⟨b₁, b₂⟩
  have hb' := Finset.mem_product.mp hb
  refine ⟨b₁, hb'.1, b₂, hb'.2, ?_⟩
  simpa [Finset.card_product, measurableLabelCell,
    measurableDoubleLabelCell] using hmeasure

#print axioms measurableSet_measurableDoubleLabelCell
#print axioms exists_measurableDoubleLabelCell_measure_ge_average

end

end FamilyStickyCinematicL32ContinuumDoubleMeasurableBucketV1
