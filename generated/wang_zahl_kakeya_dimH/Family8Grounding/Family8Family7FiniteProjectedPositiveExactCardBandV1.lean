import FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ENNReal

namespace Family8Family7FiniteProjectedPositiveExactCardBandV1

open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

universe u v

/-!
# A positive active region contains a positive exact-card band

This is the finite measurable pigeonhole needed before choosing a genuine
positive fibre floor.  It makes no geometric or quantitative claim about
which positive cardinality is selected.
-/

theorem exists_positive_exactCard_multiplicityBand
    {point : Type u} {index : Type v}
    [MeasurableSpace point] [Fintype index] [DecidableEq index]
    (mu : Measure point) (Z : FiniteProjectedShading point index)
    (hpositive : 0 < mu
      {x | x ∈ Z.base ∧ (Z.activeAtPoint x).Nonempty}) :
    ∃ n : Nat, 1 ≤ n ∧ n ≤ Z.ambient.card ∧
      0 < mu (Z.multiplicityBand n n) := by
  let cardAt : point → Nat := fun x => (Z.activeAtPoint x).card
  let E : Set point := {x | x ∈ Z.base ∧ 1 ≤ cardAt x}
  let labels : Finset Nat := Finset.Icc 1 Z.ambient.card
  have hcardMeasurable : Measurable cardAt :=
    Z.measurable_activeValue fun s => s.card
  have hE : MeasurableSet E := by
    exact Z.measurable_base.inter <|
      hcardMeasurable (Set.to_countable {n : Nat | 1 ≤ n}).measurableSet
  have hpositiveE : 0 < mu E := by
    simpa only [E, cardAt, Finset.one_le_card] using hpositive
  have hEnonempty : E.Nonempty :=
    nonempty_of_measure_ne_zero hpositiveE.ne'
  obtain ⟨x, hxE⟩ := hEnonempty
  have hxActive : (Z.activeAtPoint x).Nonempty := by
    exact Finset.one_le_card.mp hxE.2
  have hambientCard : 1 ≤ Z.ambient.card := by
    exact (Finset.one_le_card.mpr hxActive).trans
      (Finset.card_le_card
        (finiteIncidenceActiveAtPoint_subset Z.ambient
          (fun i x => x ∈ Z.carrier i) x))
  have hlabels : labels.Nonempty := by
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hambientCard⟩⟩
  have hrange : ∀ x, x ∈ E → cardAt x ∈ labels := by
    intro x hx
    apply Finset.mem_Icc.mpr
    refine ⟨hx.2, ?_⟩
    exact Finset.card_le_card
      (finiteIncidenceActiveAtPoint_subset Z.ambient
        (fun i x => x ∈ Z.carrier i) x)
  obtain ⟨n, hn, hmeasure⟩ :=
    exists_measurableLabelCell_measure_ge_average mu labels hlabels hE
      hcardMeasurable hrange
  have haveragePos : 0 < mu E / (labels.card : ENNReal) :=
    ENNReal.div_pos hpositiveE.ne' (ENNReal.natCast_ne_top _)
  have hcellPos : 0 < mu (measurableLabelCell E cardAt n) :=
    haveragePos.trans_le hmeasure
  have hcellEq : measurableLabelCell E cardAt n =
      Z.multiplicityBand n n := by
    ext y
    rw [FiniteProjectedShading.mem_multiplicityBand]
    simp only [measurableLabelCell, E, cardAt, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hyBase, _hyPos⟩, hyCard⟩
      exact ⟨hyBase, by omega, by omega⟩
    · rintro ⟨hyBase, hnLower, hnUpper⟩
      have hyCard : (Z.activeAtPoint y).card = n := by omega
      have hnPos : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact ⟨⟨hyBase, by omega⟩, hyCard⟩
  refine ⟨n, (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2, ?_⟩
  rwa [← hcellEq]

#print axioms exists_positive_exactCard_multiplicityBand

end

end Family8Family7FiniteProjectedPositiveExactCardBandV1
