import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41AlternatingSignIccThreeRootsV1

open FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1

/-!
# Four alternating signs contradict an `Icc` root bound of two

The scalar IVT core produces one root in each of three intervening open
intervals.  If the first and last samples lie in the ambient paper interval,
all three roots lie there as well, so the *restricted* root set has extended
cardinality at least three.
-/

theorem not_Icc_rootSet_encard_le_two_of_alternatingStrictSign
    (f : Real -> Real) {A B a b c d : Real}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ Icc A B) (hd : d ∈ Icc A B)
    (hcontinuous : ContinuousOn f (Icc a d))
    (hsign : AlternatingStrictSign f a b c d) :
    ¬ ({z : Real | z ∈ Icc A B ∧ f z = 0} : Set Real).encard ≤ 2 := by
  rintro hle
  obtain ⟨z0, z1, z2, hz0, hz1, hz2, hroot0, hroot1, hroot2⟩ :=
    exists_three_interval_roots_of_alternatingStrictSign
      f hab hbc hcd hcontinuous hsign
  have hz0AB : z0 ∈ Icc A B := by
    constructor
    · exact ha.1.trans hz0.1.le
    · exact hz0.2.le.trans (hbc.trans hcd).le |>.trans hd.2
  have hz1AB : z1 ∈ Icc A B := by
    constructor
    · exact ha.1.trans (hab.trans hz1.1).le
    · exact hz1.2.le.trans hcd.le |>.trans hd.2
  have hz2AB : z2 ∈ Icc A B := by
    constructor
    · exact ha.1.trans (hab.trans hbc |>.trans hz2.1).le
    · exact hz2.2.le.trans hd.2
  have hz01 : z0 < z1 := hz0.2.trans hz1.1
  have hz12 : z1 < z2 := hz1.2.trans hz2.1
  have hsub : ({z0, z1, z2} : Set Real) ⊆
      {z : Real | z ∈ Icc A B ∧ f z = 0} := by
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨hz0AB, hroot0⟩
    · exact ⟨hz1AB, hroot1⟩
    · exact ⟨hz2AB, hroot2⟩
  have hcard : ({z0, z1, z2} : Set Real).encard = 3 := by
    rw [encard_insert_of_notMem, encard_insert_of_notMem, encard_singleton]
    · norm_num
    · simp [ne_of_lt hz12]
    · simp [ne_of_lt hz01, ne_of_lt (hz01.trans hz12)]
  have hthree : (3 : ℕ∞) ≤
      ({z : Real | z ∈ Icc A B ∧ f z = 0} : Set Real).encard := by
    rw [← hcard]
    exact encard_le_encard hsub
  have hbad : (3 : ℕ∞) ≤ 2 := hthree.trans hle
  norm_num at hbad

#print axioms not_Icc_rootSet_encard_le_two_of_alternatingStrictSign

end FamilyStickyCinematicL32Prop41AlternatingSignIccThreeRootsV1
