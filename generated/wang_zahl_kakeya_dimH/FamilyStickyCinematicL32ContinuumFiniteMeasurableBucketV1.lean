import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1

noncomputable section

/-!
# A measure pigeonhole theorem for a finite measurable label

This is the continuum counterpart of the finite-item bucket lemmas used later
in the cinematic argument.  The points being bucketed need not form a finite
set.  What is finite is the label range, and measurability of the label is an
explicit source obligation.
-/

universe u v

variable {X : Type u} {labelType : Type v}
  [MeasurableSpace X] [MeasurableSpace labelType]
  [MeasurableSingletonClass labelType]

/-- The part of `E` with one prescribed finite label. -/
def measurableLabelCell (E : Set X) (label : X → labelType)
    (b : labelType) : Set X :=
  E ∩ label ⁻¹' {b}

theorem measurableSet_measurableLabelCell
    {E : Set X} {label : X → labelType}
    (hE : MeasurableSet E) (hlabel : Measurable label)
    (b : labelType) :
    MeasurableSet (measurableLabelCell E label b) := by
  exact hE.inter (hlabel (measurableSet_singleton b))

omit [MeasurableSpace X] [MeasurableSpace labelType]
    [MeasurableSingletonClass labelType] in
theorem pairwiseDisjoint_measurableLabelCell
    (E : Set X) (label : X → labelType)
    (labels : Finset labelType) :
    Set.PairwiseDisjoint (labels : Set labelType)
      (measurableLabelCell E label) := by
  classical
  intro b hb c hc hbc
  change Disjoint (measurableLabelCell E label b)
    (measurableLabelCell E label c)
  rw [Set.disjoint_left]
  intro x hxb hxc
  have hbx : label x = b := by
    simpa [measurableLabelCell] using hxb.2
  have hcx : label x = c := by
    simpa [measurableLabelCell] using hxc.2
  exact hbc (hbx.symm.trans hcx)

omit [MeasurableSpace X] [MeasurableSpace labelType]
    [MeasurableSingletonClass labelType] in
theorem biUnion_measurableLabelCell_eq
    (E : Set X) (label : X → labelType)
    (labels : Finset labelType)
    (hrange : ∀ x ∈ E, label x ∈ labels) :
    (⋃ b ∈ (labels : Set labelType), measurableLabelCell E label b) = E := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨b, _hb, hcell⟩
    exact hcell.1
  · intro x hx
    have hb : label x ∈ labels := hrange x hx
    simp only [Set.mem_iUnion]
    exact ⟨label x, hb, hx, by simp⟩

/-- Exact measure decomposition into finitely many measurable label cells. -/
theorem measure_eq_sum_measurableLabelCell
    (μ : Measure X) {E : Set X} {label : X → labelType}
    (labels : Finset labelType)
    (hE : MeasurableSet E) (hlabel : Measurable label)
    (hrange : ∀ x ∈ E, label x ∈ labels) :
    μ E = ∑ b ∈ labels, μ (measurableLabelCell E label b) := by
  calc
    μ E = μ (⋃ b ∈ (labels : Set labelType),
        measurableLabelCell E label b) := by
      rw [biUnion_measurableLabelCell_eq E label labels hrange]
    _ = ∑ b ∈ labels, μ (measurableLabelCell E label b) := by
      exact measure_biUnion_finset
        (pairwiseDisjoint_measurableLabelCell E label labels)
        (fun b _hb => measurableSet_measurableLabelCell hE hlabel b)

/-- A finite measurable label retains at least the average measure.  The
denominator is the actual number of admitted labels, not an arbitrary ambient
finite type. -/
theorem exists_measurableLabelCell_measure_ge_average
    (μ : Measure X) {E : Set X} {label : X → labelType}
    (labels : Finset labelType)
    (hlabels : labels.Nonempty)
    (hE : MeasurableSet E) (hlabel : Measurable label)
    (hrange : ∀ x ∈ E, label x ∈ labels) :
    ∃ b ∈ labels,
      μ E / (labels.card : ENNReal) ≤
        μ (measurableLabelCell E label b) := by
  classical
  let cellMass : labelType → ENNReal :=
    fun b => μ (measurableLabelCell E label b)
  obtain ⟨b, hb, hmax⟩ :=
    Finset.exists_max_image labels cellMass hlabels
  have hsum :
      (∑ c ∈ labels, cellMass c) ≤ labels.card • cellMass b :=
    Finset.sum_le_card_nsmul labels cellMass (cellMass b)
      (fun c hc => hmax c hc)
  have htotal : μ E ≤ (labels.card : ENNReal) * cellMass b := by
    rw [measure_eq_sum_measurableLabelCell μ labels hE hlabel hrange]
    simpa [cellMass, nsmul_eq_mul] using hsum
  refine ⟨b, hb, ?_⟩
  rw [ENNReal.div_le_iff]
  · simpa [cellMass, mul_comm] using htotal
  · simp [Finset.card_ne_zero.mpr hlabels]
  · simp

#print axioms measurableSet_measurableLabelCell
#print axioms pairwiseDisjoint_measurableLabelCell
#print axioms biUnion_measurableLabelCell_eq
#print axioms measure_eq_sum_measurableLabelCell
#print axioms exists_measurableLabelCell_measure_ge_average

end

end FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
