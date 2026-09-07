import FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Exact-card selection after an explicit fibre truncation

This file isolates the finite-cardinality step needed after a high-fibre
truncation has already retained weighted mass.  It makes no dyadic choice and
introduces no scale counter: the only labels are the literal values of
`activeAtPoint.card` in `1, ..., Z.ambient.card`.

The theorem is deliberately stated for an arbitrary measurable weight.  A
later wrapper can instantiate it with the explicit-truncation
`highFibreWeightedMultiplicity`; the support hypothesis then follows directly
from the positive-lower carrier definition.  In particular, the selected set
uses the very same `Z` and cannot reselect a graph or any geometric witness.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Family8ExplicitTruncationHighFibreExactCardV1

open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

universe u v

variable {point : Type u} {index : Type v}
  [MeasurableSpace point]

/-- Finite exact-card averaging for a measurable weighted high-fibre set.

The support condition is the weakest geometric input: wherever the weight is
nonzero inside `E`, the point belongs to the base of the same projected datum
and has a nonempty active pattern.  No upper fibre bound, dyadic bucket, or
finiteness of the weighted mass is used.
-/
theorem exists_exactCard_weightedMass_ge_average
    (μ : Measure point)
    (Z : FiniteProjectedShading point index)
    (w : point → ENNReal) (hw : Measurable w)
    (E : Set point) (hE : MeasurableSet E)
    (hambient : 1 ≤ Z.ambient.card)
    (hsupport : ∀ x ∈ E, w x ≠ 0 →
      x ∈ Z.base ∧ (Z.activeAtPoint x).Nonempty) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ Z.ambient.card ∧
      (μ.withDensity w) E ≤
        (Z.ambient.card : ENNReal) *
          (μ.withDensity w) (E ∩ Z.multiplicityBand p p) := by
  classical
  let weightedMeasure : Measure point := μ.withDensity w
  let cardAt : point → Nat := fun x ↦ (Z.activeAtPoint x).card
  let positiveBase : Set point :=
    Z.base ∩ {x | 1 ≤ cardAt x}
  let R : Set point := E ∩ positiveBase
  let labels : Finset Nat := Finset.Icc 1 Z.ambient.card
  have hcardMeasurable : Measurable cardAt :=
    Z.measurable_activeValue fun s ↦ s.card
  have hpositiveBase : MeasurableSet positiveBase := by
    exact Z.measurable_base.inter <|
      hcardMeasurable
        (Set.to_countable {k : Nat | 1 ≤ k}).measurableSet
  have hR : MeasurableSet R := hE.inter hpositiveBase
  have hRsubset : R ⊆ E := Set.inter_subset_left
  have hdiffZero : weightedMeasure (E \ R) = 0 := by
    change (μ.withDensity w) (E \ R) = 0
    apply (MeasureTheory.withDensity_apply_eq_zero hw).2
    have hempty : {x : point | w x ≠ 0} ∩ (E \ R) = ∅ := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hx with ⟨hwx, hxE, hxNotR⟩
        have hxSupport := hsupport x hxE hwx
        have hxPositive : 1 ≤ cardAt x := by
          exact Finset.one_le_card.mpr hxSupport.2
        exact (hxNotR ⟨hxE, hxSupport.1, hxPositive⟩).elim
      · exact Set.empty_subset _
    rw [hempty, measure_empty]
  have hweightedR : weightedMeasure R = weightedMeasure E :=
    measure_eq_measure_of_null_sdiff hRsubset hdiffZero
  have hlabels : labels.Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hambient⟩⟩
  have hrange : ∀ x, x ∈ R → cardAt x ∈ labels := by
    intro x hx
    apply Finset.mem_Icc.mpr
    refine ⟨hx.2.2, ?_⟩
    exact Finset.card_le_card
      (finiteIncidenceActiveAtPoint_subset Z.ambient
        (fun i y ↦ y ∈ Z.carrier i) x)
  let cellMass : Nat → ENNReal :=
    fun p ↦ weightedMeasure (measurableLabelCell R cardAt p)
  obtain ⟨p, hp, hmax⟩ :=
    Finset.exists_max_image labels cellMass hlabels
  have hsum : (∑ k ∈ labels, cellMass k) ≤
      labels.card • cellMass p :=
    Finset.sum_le_card_nsmul labels cellMass (cellMass p)
      (fun k hk ↦ hmax k hk)
  have htotalR : weightedMeasure R ≤
      (labels.card : ENNReal) *
        weightedMeasure (measurableLabelCell R cardAt p) := by
    rw [measure_eq_sum_measurableLabelCell
      weightedMeasure labels hR hcardMeasurable hrange]
    simpa only [cellMass, nsmul_eq_mul] using hsum
  have hpData := Finset.mem_Icc.mp hp
  have hlabelsCard : labels.card = Z.ambient.card := by
    simp [labels]
  have hcellEq : measurableLabelCell R cardAt p =
      E ∩ Z.multiplicityBand p p := by
    ext x
    simp only [Set.mem_inter_iff]
    rw [FiniteProjectedShading.mem_multiplicityBand]
    simp only [measurableLabelCell, R, positiveBase, cardAt,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hxE, hxBase, _hxPositive⟩, hxCard⟩
      exact ⟨hxE, hxBase, by omega, by omega⟩
    · rintro ⟨hxE, hxBase, hpLower, hpUpper⟩
      have hxCard : (Z.activeAtPoint x).card = p := by omega
      have hxPositive : 1 ≤ cardAt x := by
        simpa only [cardAt, hxCard] using hpData.1
      exact ⟨⟨hxE, hxBase, hxPositive⟩, by
        simpa only [cardAt] using hxCard⟩
  refine ⟨p, hpData.1, hpData.2, ?_⟩
  calc
    (μ.withDensity w) E = weightedMeasure R := hweightedR.symm
    _ ≤ (labels.card : ENNReal) *
        weightedMeasure (measurableLabelCell R cardAt p) := htotalR
    _ = (Z.ambient.card : ENNReal) *
        weightedMeasure (E ∩ Z.multiplicityBand p p) := by
      rw [hlabelsCard, hcellEq]
    _ = (Z.ambient.card : ENNReal) *
        (μ.withDensity w) (E ∩ Z.multiplicityBand p p) := by rfl

#print axioms exists_exactCard_weightedMass_ge_average

end

end Family8ExplicitTruncationHighFibreExactCardV1
