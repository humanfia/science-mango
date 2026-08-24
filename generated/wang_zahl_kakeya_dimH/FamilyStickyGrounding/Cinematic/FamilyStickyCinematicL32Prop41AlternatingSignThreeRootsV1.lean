import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1

/-!
# Four alternating signs force three distinct roots

This is the scalar continuous core used after the finite `K_{2,3}` interval
order obstruction.  Strict alternating signs at four ordered samples give
one root in each intervening open interval, and hence root-set encard at
least three.
-/

theorem exists_root_Ioo_of_strict_sign_change
    (f : Real -> Real) {a b : Real} (hab : a < b)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hsign : (f a < 0 /\ 0 < f b) \/ (f b < 0 /\ 0 < f a)) :
    exists z, z ∈ Ioo a b /\ f z = 0 := by
  rcases hsign with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hab.le hcontinuous
      (show (0 : Real) ∈ Icc (f a) (f b) from ⟨ha.le, hb.le⟩)
    have hza : z ≠ a := by
      intro h
      subst z
      linarith
    have hzb : z ≠ b := by
      intro h
      subst z
      linarith
    exact ⟨z, ⟨lt_of_le_of_ne hz.1 hza.symm, lt_of_le_of_ne hz.2 hzb⟩, hz0⟩
  · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hab.le hcontinuous
      (show (0 : Real) ∈ Icc (f b) (f a) from ⟨hb.le, ha.le⟩)
    have hza : z ≠ a := by
      intro h
      subst z
      linarith
    have hzb : z ≠ b := by
      intro h
      subst z
      linarith
    exact ⟨z, ⟨lt_of_le_of_ne hz.1 hza.symm, lt_of_le_of_ne hz.2 hzb⟩, hz0⟩

def AlternatingStrictSign (f : Real -> Real) (a b c d : Real) : Prop :=
  (f a < 0 /\ 0 < f b /\ f c < 0 /\ 0 < f d) \/
    (0 < f a /\ f b < 0 /\ 0 < f c /\ f d < 0)

theorem exists_three_interval_roots_of_alternatingStrictSign
    (f : Real -> Real) {a b c d : Real}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hcontinuous : ContinuousOn f (Icc a d))
    (hsign : AlternatingStrictSign f a b c d) :
    exists z0 z1 z2,
      z0 ∈ Ioo a b /\ z1 ∈ Ioo b c /\ z2 ∈ Ioo c d /\
      f z0 = 0 /\ f z1 = 0 /\ f z2 = 0 := by
  have habSub : Icc a b ⊆ Icc a d :=
    Icc_subset_Icc le_rfl (hbc.trans hcd).le
  have hbcSub : Icc b c ⊆ Icc a d :=
    Icc_subset_Icc hab.le hcd.le
  have hcdSub : Icc c d ⊆ Icc a d :=
    Icc_subset_Icc (hab.trans hbc).le le_rfl
  rcases hsign with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
  · obtain ⟨z0, hz0, hroot0⟩ := exists_root_Ioo_of_strict_sign_change
      f hab (hcontinuous.mono habSub) (Or.inl ⟨ha, hb⟩)
    obtain ⟨z1, hz1, hroot1⟩ := exists_root_Ioo_of_strict_sign_change
      f hbc (hcontinuous.mono hbcSub) (Or.inr ⟨hc, hb⟩)
    obtain ⟨z2, hz2, hroot2⟩ := exists_root_Ioo_of_strict_sign_change
      f hcd (hcontinuous.mono hcdSub) (Or.inl ⟨hc, hd⟩)
    exact ⟨z0, z1, z2, hz0, hz1, hz2, hroot0, hroot1, hroot2⟩
  · obtain ⟨z0, hz0, hroot0⟩ := exists_root_Ioo_of_strict_sign_change
      f hab (hcontinuous.mono habSub) (Or.inr ⟨hb, ha⟩)
    obtain ⟨z1, hz1, hroot1⟩ := exists_root_Ioo_of_strict_sign_change
      f hbc (hcontinuous.mono hbcSub) (Or.inl ⟨hb, hc⟩)
    obtain ⟨z2, hz2, hroot2⟩ := exists_root_Ioo_of_strict_sign_change
      f hcd (hcontinuous.mono hcdSub) (Or.inr ⟨hd, hc⟩)
    exact ⟨z0, z1, z2, hz0, hz1, hz2, hroot0, hroot1, hroot2⟩

theorem three_le_rootSet_encard_of_interval_roots
    (f : Real -> Real) {a b c d z0 z1 z2 : Real}
    (hz0 : z0 ∈ Ioo a b) (hz1 : z1 ∈ Ioo b c)
    (hz2 : z2 ∈ Ioo c d)
    (hroot0 : f z0 = 0) (hroot1 : f z1 = 0) (hroot2 : f z2 = 0) :
    (3 : ℕ∞) ≤ ({z : Real | f z = 0} : Set Real).encard := by
  have hz01 : z0 < z1 := hz0.2.trans hz1.1
  have hz12 : z1 < z2 := hz1.2.trans hz2.1
  have hsub : ({z0, z1, z2} : Set Real) ⊆ {z : Real | f z = 0} := by
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hroot0
    · exact hroot1
    · exact hroot2
  have hcard : ({z0, z1, z2} : Set Real).encard = 3 := by
    rw [encard_insert_of_notMem, encard_insert_of_notMem, encard_singleton]
    · norm_num
    · simp [ne_of_lt hz12]
    · simp [ne_of_lt hz01, ne_of_lt (hz01.trans hz12)]
  rw [← hcard]
  exact encard_le_encard hsub

theorem not_rootSet_encard_le_two_of_alternatingStrictSign
    (f : Real -> Real) {a b c d : Real}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hcontinuous : ContinuousOn f (Icc a d))
    (hsign : AlternatingStrictSign f a b c d) :
    ¬ ({z : Real | f z = 0} : Set Real).encard ≤ 2 := by
  rintro hle
  obtain ⟨z0, z1, z2, hz0, hz1, hz2, hroot0, hroot1, hroot2⟩ :=
    exists_three_interval_roots_of_alternatingStrictSign
      f hab hbc hcd hcontinuous hsign
  have hthree := three_le_rootSet_encard_of_interval_roots
    f hz0 hz1 hz2 hroot0 hroot1 hroot2
  have hbad : (3 : ℕ∞) ≤ 2 := hthree.trans hle
  norm_num at hbad

#print axioms exists_root_Ioo_of_strict_sign_change
#print axioms exists_three_interval_roots_of_alternatingStrictSign
#print axioms three_le_rootSet_encard_of_interval_roots
#print axioms not_rootSet_encard_le_two_of_alternatingStrictSign

end FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1
