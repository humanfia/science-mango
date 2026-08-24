import FamilyStickyCinematicL32FiniteWeightedBucketV1
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

/-!
# The actual dyadic ceil bucket for PYZ two-ends scales

For a positive radius `r`, the label is `ceil(log_2 r)` and its upper
endpoint is `2^label`.  The ceil convention gives the exact half-open bin
`(upper/2, upper]`, including the strict lower inequality needed by the
dyadic two-ends facade.
-/

/-- Integer label of the half-open dyadic bin containing `r`. -/
noncomputable def dyadicCeilBucket (r : Real) : Int :=
  ⌈Real.logb 2 r⌉

/-- Upper endpoint attached to a dyadic label. -/
def dyadicCeilUpper (label : Int) : Real :=
  (2 : Real) ^ (label : Real)

/-- Every positive radius lies in the literal half-open bin selected by
its ceil-log label. -/
theorem dyadicCeilUpper_half_lt_and_le
    {r : Real} (hr : 0 < r) :
    dyadicCeilUpper (dyadicCeilBucket r) / 2 < r ∧
      r <= dyadicCeilUpper (dyadicCeilBucket r) := by
  let y := Real.logb 2 r
  let label := ⌈y⌉
  have hyLower : ((label : Int) : Real) - 1 < y := by
    have hceil := Int.ceil_lt_add_one y
    dsimp only [label]
    linarith
  have hyUpper : y <= ((label : Int) : Real) := by
    exact Int.le_ceil y
  have hpowLower :
      (2 : Real) ^ (((label : Int) : Real) - 1) < r :=
    (Real.lt_logb_iff_rpow_lt (b := (2 : Real))
      (by norm_num) hr).mp hyLower
  have hpowUpper :
      r <= (2 : Real) ^ ((label : Int) : Real) :=
    (Real.logb_le_iff_le_rpow (b := (2 : Real))
      (by norm_num) hr).mp hyUpper
  constructor
  · change (2 : Real) ^ ((label : Int) : Real) / 2 < r
    rw [← Real.rpow_sub_one (by norm_num : (2 : Real) ≠ 0)]
    exact hpowLower
  · exact hpowUpper

/-- The ceil-log dyadic label is monotone on positive radii. -/
theorem dyadicCeilBucket_mono
    {r s : Real} (hr : 0 < r) (hrs : r <= s) :
    dyadicCeilBucket r <= dyadicCeilBucket s := by
  apply Int.ceil_mono
  exact Real.logb_le_logb_of_le (b := (2 : Real))
    (by norm_num) hr hrs

/-- Occupied dyadic labels of radii contained in `[delta,K]` fit in the
corresponding explicit integer interval. -/
theorem occupied_dyadicCeilBuckets_subset_Icc
    {item : Type*} (items : Finset item) (scale : item -> Real)
    {delta K : Real} (hdelta : 0 < delta)
    (hscale : forall x, x ∈ items -> delta <= scale x ∧ scale x <= K) :
    occupiedWeightBuckets items (fun x => dyadicCeilBucket (scale x)) ⊆
      Finset.Icc (dyadicCeilBucket delta) (dyadicCeilBucket K) := by
  intro label hlabel
  rcases mem_occupiedWeightBuckets_iff.mp hlabel with ⟨x, hx, rfl⟩
  rw [Finset.mem_Icc]
  have hxBounds := hscale x hx
  have hxPositive : 0 < scale x := hdelta.trans_le hxBounds.1
  exact ⟨dyadicCeilBucket_mono hdelta hxBounds.1,
    dyadicCeilBucket_mono hxPositive hxBounds.2⟩

/-- Explicit cardinal bound for the occupied dyadic scale labels. -/
theorem card_occupied_dyadicCeilBuckets_le
    {item : Type*} (items : Finset item) (scale : item -> Real)
    {delta K : Real} (hdelta : 0 < delta)
    (hscale : forall x, x ∈ items -> delta <= scale x ∧ scale x <= K) :
    (occupiedWeightBuckets items
      (fun x => dyadicCeilBucket (scale x))).card <=
      (dyadicCeilBucket K + 1 - dyadicCeilBucket delta).toNat := by
  calc
    (occupiedWeightBuckets items
        (fun x => dyadicCeilBucket (scale x))).card <=
        (Finset.Icc (dyadicCeilBucket delta)
          (dyadicCeilBucket K)).card :=
      Finset.card_le_card
        (occupied_dyadicCeilBuckets_subset_Icc items scale hdelta hscale)
    _ = (dyadicCeilBucket K + 1 - dyadicCeilBucket delta).toNat :=
      Int.card_Icc (dyadicCeilBucket delta) (dyadicCeilBucket K)

#print axioms dyadicCeilBucket
#print axioms dyadicCeilUpper
#print axioms dyadicCeilUpper_half_lt_and_le
#print axioms dyadicCeilBucket_mono
#print axioms occupied_dyadicCeilBuckets_subset_Icc
#print axioms card_occupied_dyadicCeilBuckets_le

end

end FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
