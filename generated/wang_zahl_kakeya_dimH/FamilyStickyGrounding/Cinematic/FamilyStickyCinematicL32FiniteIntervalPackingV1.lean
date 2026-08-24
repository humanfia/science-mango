import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteIntervalPackingV1

open scoped BigOperators

noncomputable section

/-!
# Finite packing of disjoint rectangle base intervals

This is the first one-dimensional packing bridge toward
Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.15 as used in Lemma 5.8.
Once geometric incomparability produces a disjoint (or bounded-overlap)
family of rectangle base intervals, containment in a short sublevel set
turns directly into a cardinality bound.

The present theorem proves the exact disjoint finite case.  It does not
assume a rectangle-count conclusion or the later lens bound.
-/

/-- Pairwise-disjoint open intervals of length at least `ell`, all contained
in `target`, occupy at least `#indices * ell` volume in `target`.  Open bases
allow adjacent closed rectangle bases to share endpoints without affecting
the packing measure. -/
theorem card_mul_intervalLength_le_volume
    {index : Type*} (indices : Finset index)
    (left right : index -> Real) (target : Set Real) {ell : Real}
    (_hell : 0 <= ell)
    (hlength : forall i, i ∈ indices -> ell <= right i - left i)
    (hdisjoint : Set.PairwiseDisjoint (indices : Set index)
      (fun i => Ioo (left i) (right i)))
    (hsubset : forall i, i ∈ indices ->
      Ioo (left i) (right i) ⊆ target) :
    (indices.card : ENNReal) * ENNReal.ofReal ell <= volume target := by
  have hpiece : forall i, i ∈ indices ->
      ENNReal.ofReal ell <= volume (Ioo (left i) (right i)) := by
    intro i hi
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal (hlength i hi)
  have hunionSubset :
      (⋃ i ∈ (indices : Set index), Ioo (left i) (right i)) ⊆ target := by
    intro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨i, hi, hx⟩
    exact hsubset i hi hx
  calc
    (indices.card : ENNReal) * ENNReal.ofReal ell =
        ∑ _i ∈ indices, ENNReal.ofReal ell := by
      simp [nsmul_eq_mul]
    _ <= ∑ i ∈ indices, volume (Ioo (left i) (right i)) := by
      exact Finset.sum_le_sum hpiece
    _ = volume (⋃ i ∈ (indices : Set index),
        Ioo (left i) (right i)) := by
      exact (measure_biUnion_finset hdisjoint
        (fun _i _hi => measurableSet_Ioo)).symm
    _ <= volume target := volume.mono hunionSubset

/-- If the target already has an explicit volume upper bound, the finite
packing gives the corresponding denominator-free cardinal inequality. -/
theorem card_mul_intervalLength_le_of_volume_le
    {index : Type*} (indices : Finset index)
    (left right : index -> Real) (target : Set Real) {ell bound : Real}
    (_hell : 0 <= ell)
    (hlength : forall i, i ∈ indices -> ell <= right i - left i)
    (hdisjoint : Set.PairwiseDisjoint (indices : Set index)
      (fun i => Ioo (left i) (right i)))
    (hsubset : forall i, i ∈ indices ->
      Ioo (left i) (right i) ⊆ target)
    (hvolume : volume target <= ENNReal.ofReal bound) :
    (indices.card : ENNReal) * ENNReal.ofReal ell <=
      ENNReal.ofReal bound :=
  (card_mul_intervalLength_le_volume
      indices left right target _hell hlength hdisjoint hsubset).trans hvolume

#print axioms card_mul_intervalLength_le_volume
#print axioms card_mul_intervalLength_le_of_volume_le

end

end FamilyStickyCinematicL32FiniteIntervalPackingV1
