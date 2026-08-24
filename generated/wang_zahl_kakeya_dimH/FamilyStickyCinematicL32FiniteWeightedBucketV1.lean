import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace FamilyStickyCinematicL32FiniteWeightedBucketV1

open scoped BigOperators

noncomputable section

/-!
# Finite weighted bucket pigeonholing

This is the pure finite weighted-pigeonhole step used in the dyadic
shading-size selection of Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 5.5 (the classes `R(j)` in its proof).
The bucket carrying average total weight is produced below rather than
assumed.  No geometric rectangle count or measure estimate enters.
-/

/-- The finite set of bucket labels actually occupied by `items`. -/
noncomputable def occupiedWeightBuckets {alpha beta : Type*}
    (items : Finset alpha) (bucket : alpha -> beta) : Finset beta := by
  classical
  exact items.image bucket

/-- Total weight in one finite bucket fiber. -/
noncomputable def bucketWeight {alpha beta : Type*}
    (items : Finset alpha) (bucket : alpha -> beta)
    (weight : alpha -> Real) (label : beta) : Real := by
  classical
  exact ∑ x ∈ items with bucket x = label, weight x

@[simp]
theorem mem_occupiedWeightBuckets_iff {alpha beta : Type*}
    {items : Finset alpha} {bucket : alpha -> beta} {label : beta} :
    label ∈ occupiedWeightBuckets items bucket ↔
      exists x, x ∈ items ∧ bucket x = label := by
  classical
  simp [occupiedWeightBuckets]

/-- Nonempty finite data has a nonempty occupied-label set. -/
theorem occupiedWeightBuckets_nonempty {alpha beta : Type*}
    {items : Finset alpha} {bucket : alpha -> beta}
    (hitems : items.Nonempty) :
    (occupiedWeightBuckets items bucket).Nonempty := by
  classical
  simpa [occupiedWeightBuckets] using hitems.image bucket

/-- Weighted finite pigeonhole with an explicit threshold. -/
theorem exists_bucketWeight_ge {alpha beta : Type*}
    {items : Finset alpha} {bucket : alpha -> beta}
    (weight : alpha -> Real) (hitems : items.Nonempty)
    (threshold : Real)
    (hthreshold :
      ((occupiedWeightBuckets items bucket).card : Real) * threshold <=
        ∑ x ∈ items, weight x) :
    exists label, label ∈ occupiedWeightBuckets items bucket ∧
      threshold <= bucketWeight items bucket weight label := by
  classical
  have hmaps : forall x, x ∈ items ->
      bucket x ∈ occupiedWeightBuckets items bucket := by
    intro x hx
    exact mem_occupiedWeightBuckets_iff.mpr ⟨x, hx, rfl⟩
  have hthreshold' :
      (occupiedWeightBuckets items bucket).card • threshold <=
        ∑ x ∈ items, weight x := by
    simpa [nsmul_eq_mul] using hthreshold
  rcases Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (M := Real) (s := items)
      (t := occupiedWeightBuckets items bucket)
      (f := bucket) (w := weight)
      hmaps (occupiedWeightBuckets_nonempty hitems) hthreshold' with
    ⟨label, hlabel, hweight⟩
  exact ⟨label, hlabel, by simpa [bucketWeight] using hweight⟩

/-- Some occupied bucket carries at least the exact average total weight. -/
theorem exists_bucketWeight_ge_average {alpha beta : Type*}
    {items : Finset alpha} {bucket : alpha -> beta}
    (weight : alpha -> Real) (hitems : items.Nonempty) :
    exists label, label ∈ occupiedWeightBuckets items bucket ∧
      (∑ x ∈ items, weight x) /
          (occupiedWeightBuckets items bucket).card <=
        bucketWeight items bucket weight label := by
  classical
  let labels := occupiedWeightBuckets items bucket
  have hlabels : labels.Nonempty := occupiedWeightBuckets_nonempty hitems
  have hcardNat : 0 < labels.card := Finset.card_pos.mpr hlabels
  have hcard : (labels.card : Real) ≠ 0 := by
    exact_mod_cast hcardNat.ne'
  have hthreshold :
      (labels.card : Real) *
          ((∑ x ∈ items, weight x) / labels.card) <=
        ∑ x ∈ items, weight x := by
    exact (mul_div_cancel₀ (∑ x ∈ items, weight x) hcard).le
  simpa [labels] using
    (exists_bucketWeight_ge weight hitems
      ((∑ x ∈ items, weight x) / labels.card) hthreshold)

/-- Denominator-free average form: total weight is at most the occupied
bucket count times one selected bucket's weight. -/
theorem exists_totalWeight_le_card_mul_bucketWeight
    {alpha beta : Type*}
    {items : Finset alpha} {bucket : alpha -> beta}
    (weight : alpha -> Real) (hitems : items.Nonempty) :
    exists label, label ∈ occupiedWeightBuckets items bucket ∧
      (∑ x ∈ items, weight x) <=
        (occupiedWeightBuckets items bucket).card *
          bucketWeight items bucket weight label := by
  classical
  rcases exists_bucketWeight_ge_average weight hitems with
    ⟨label, hlabel, havg⟩
  let labels := occupiedWeightBuckets items bucket
  have hlabels : labels.Nonempty := occupiedWeightBuckets_nonempty hitems
  have hcardNat : 0 < labels.card := Finset.card_pos.mpr hlabels
  have hcard : (labels.card : Real) ≠ 0 := by
    exact_mod_cast hcardNat.ne'
  have hcardNonneg : (0 : Real) <= labels.card := by
    exact_mod_cast (Nat.zero_le labels.card)
  refine ⟨label, hlabel, ?_⟩
  calc
    (∑ x ∈ items, weight x) =
        (labels.card : Real) *
          ((∑ x ∈ items, weight x) / labels.card) :=
      (mul_div_cancel₀ (∑ x ∈ items, weight x) hcard).symm
    _ <= (labels.card : Real) *
        bucketWeight items bucket weight label :=
      mul_le_mul_of_nonneg_left (by simpa [labels] using havg) hcardNonneg
    _ = (occupiedWeightBuckets items bucket).card *
        bucketWeight items bucket weight label := by rfl

#print axioms mem_occupiedWeightBuckets_iff
#print axioms occupiedWeightBuckets_nonempty
#print axioms exists_bucketWeight_ge
#print axioms exists_bucketWeight_ge_average
#print axioms exists_totalWeight_le_card_mul_bucketWeight

end

end FamilyStickyCinematicL32FiniteWeightedBucketV1
