import Mathlib.Tactic

/-!
# Exact-value bucketing for finite ENNReal weights

An arbitrary finite nonnegative weight need not be pointwise comparable on
its whole support.  Bucketing by the literal weight value gives a canonical
finite remedy: one occupied value class retains total weight up to the number
of occupied values, hence up to the source cardinality.  If the total weight
is nonzero, the selected class is nonempty and its common value is positive.

This is the finite selection needed before cancelling an occurrence weight
from a weighted critical-score inequality.  No geometric or desired
nonconcentration conclusion is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace Family8FiniteENNRealExactWeightBucketV1

noncomputable section

/-- The finite set of weight values actually occupied by `source`. -/
def occupiedExactWeightValues {alpha : Type*}
    (source : Finset alpha) (weight : alpha -> ENNReal) : Finset ENNReal := by
  classical
  exact source.image weight

/-- The literal source fibre on one exact weight value. -/
def exactWeightFiber {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha -> ENNReal)
    (value : ENNReal) : Finset alpha :=
  source.filter fun i => weight i = value

@[simp] theorem mem_occupiedExactWeightValues_iff
    {alpha : Type*} {source : Finset alpha} {weight : alpha -> ENNReal}
    {value : ENNReal} :
    value ∈ occupiedExactWeightValues source weight ↔
      ∃ i, i ∈ source ∧ weight i = value := by
  classical
  simp [occupiedExactWeightValues]

@[simp] theorem mem_exactWeightFiber_iff
    {alpha : Type*} [DecidableEq alpha]
    {source : Finset alpha} {weight : alpha -> ENNReal}
    {value : ENNReal} {i : alpha} :
    i ∈ exactWeightFiber source weight value ↔
      i ∈ source ∧ weight i = value := by
  simp [exactWeightFiber]

theorem occupiedExactWeightValues_nonempty
    {alpha : Type*} {source : Finset alpha} {weight : alpha -> ENNReal}
    (hsource : source.Nonempty) :
    (occupiedExactWeightValues source weight).Nonempty := by
  classical
  simpa [occupiedExactWeightValues] using hsource.image weight

theorem occupiedExactWeightValues_card_le
    {alpha : Type*} (source : Finset alpha) (weight : alpha -> ENNReal) :
    (occupiedExactWeightValues source weight).card <= source.card := by
  classical
  exact Finset.card_image_le

/-- Some exact-value class retains total weight up to the number of occupied
values.  This is denominator-free and valid for arbitrary `ENNReal` weights,
including zero and infinity. -/
theorem exists_exactWeightFiber_totalWeight_le
    {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha -> ENNReal)
    (hsource : source.Nonempty) :
    ∃ value, value ∈ occupiedExactWeightValues source weight ∧
      (∑ i ∈ source, weight i) <=
        ((occupiedExactWeightValues source weight).card : ENNReal) *
          ∑ i ∈ exactWeightFiber source weight value, weight i := by
  classical
  let labels := occupiedExactWeightValues source weight
  let fiberMass : ENNReal -> ENNReal := fun value =>
    ∑ i ∈ exactWeightFiber source weight value, weight i
  have hlabels : labels.Nonempty :=
    occupiedExactWeightValues_nonempty hsource
  obtain ⟨value, hvalue, hmax⟩ :=
    Finset.exists_max_image labels fiberMass hlabels
  have hmaps : ∀ i, i ∈ source -> weight i ∈ labels := by
    intro i hi
    exact mem_occupiedExactWeightValues_iff.mpr ⟨i, hi, rfl⟩
  have hpartition :
      (∑ i ∈ source, weight i) = ∑ value ∈ labels, fiberMass value := by
    change (∑ i ∈ source, weight i) =
      ∑ value ∈ labels,
        ∑ i ∈ source with weight i = value, weight i
    exact (Finset.sum_fiberwise_of_maps_to
      (s := source) (t := labels) (g := weight) hmaps weight).symm
  refine ⟨value, hvalue, ?_⟩
  calc
    (∑ i ∈ source, weight i) =
        ∑ candidate ∈ labels, fiberMass candidate := hpartition
    _ <= labels.card • fiberMass value :=
      Finset.sum_le_card_nsmul labels fiberMass (fiberMass value)
        (fun candidate hcandidate => hmax candidate hcandidate)
    _ = (labels.card : ENNReal) *
        ∑ i ∈ exactWeightFiber source weight value, weight i := by
      simp only [nsmul_eq_mul]
      rfl

/-- With nonzero total weight, the retained exact-value class is genuinely
nonempty and its common value is nonzero. -/
theorem exists_nonempty_positive_exactWeightFiber
    {alpha : Type*} [DecidableEq alpha]
    (source : Finset alpha) (weight : alpha -> ENNReal)
    (hsource : source.Nonempty)
    (htotal : (∑ i ∈ source, weight i) ≠ 0) :
    ∃ value, value ∈ occupiedExactWeightValues source weight ∧
      value ≠ 0 ∧
      (exactWeightFiber source weight value).Nonempty ∧
      exactWeightFiber source weight value ⊆ source ∧
      (∀ i ∈ exactWeightFiber source weight value, weight i = value) ∧
      (∑ i ∈ source, weight i) <=
        (source.card : ENNReal) *
          ∑ i ∈ exactWeightFiber source weight value, weight i := by
  classical
  obtain ⟨value, hvalue, hretained⟩ :=
    exists_exactWeightFiber_totalWeight_le source weight hsource
  have hfiber : (exactWeightFiber source weight value).Nonempty := by
    by_contra hempty
    have hfiberEmpty : exactWeightFiber source weight value = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hfiberEmpty] at hretained
    simp only [Finset.sum_empty, mul_zero] at hretained
    exact htotal (bot_unique hretained)
  have hvalue0 : value ≠ 0 := by
    intro hzero
    have hsum0 :
        (∑ i ∈ exactWeightFiber source weight value, weight i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact (mem_exactWeightFiber_iff.mp hi).2.trans hzero
    rw [hsum0, mul_zero] at hretained
    exact htotal (bot_unique hretained)
  refine ⟨value, hvalue, hvalue0, hfiber,
    Finset.filter_subset _ _, ?_, ?_⟩
  · intro i hi
    exact (mem_exactWeightFiber_iff.mp hi).2
  · calc
      (∑ i ∈ source, weight i) <=
          ((occupiedExactWeightValues source weight).card : ENNReal) *
            ∑ i ∈ exactWeightFiber source weight value, weight i :=
        hretained
      _ <= (source.card : ENNReal) *
            ∑ i ∈ exactWeightFiber source weight value, weight i := by
        gcongr
        exact_mod_cast occupiedExactWeightValues_card_le source weight

#print axioms mem_occupiedExactWeightValues_iff
#print axioms mem_exactWeightFiber_iff
#print axioms occupiedExactWeightValues_nonempty
#print axioms occupiedExactWeightValues_card_le
#print axioms exists_exactWeightFiber_totalWeight_le
#print axioms exists_nonempty_positive_exactWeightFiber

end

end Family8FiniteENNRealExactWeightBucketV1
