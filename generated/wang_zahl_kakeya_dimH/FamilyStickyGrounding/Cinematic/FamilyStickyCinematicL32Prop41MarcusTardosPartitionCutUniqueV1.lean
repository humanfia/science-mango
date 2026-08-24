import Mathlib.Data.List.Infix
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosPartitionCutUniqueV1

/-!
# A linear block partition has at most one block crossing a cut

This is the arithmetic kernel behind the “at most one singular block pair”
part of Marcus--Tardos Lemma 2.  Blocks are position-indexed, so empty blocks
remain distinct.  No estimate is assumed here.
-/

def prefixLength {α : Type*} (blocks : List (List α)) (i : Nat) : Nat :=
  (blocks.take i).flatten.length

def CrossesCut {α : Type*} (blocks : List (List α))
    (cut : Nat) (i : Fin blocks.length) : Prop :=
  prefixLength blocks i.1 < cut ∧
    cut < prefixLength blocks (i.1 + 1)

instance decidableCrossesCut {α : Type*} (blocks : List (List α))
    (cut : Nat) (i : Fin blocks.length) :
    Decidable (CrossesCut blocks cut i) := by
  unfold CrossesCut
  infer_instance

theorem prefixLength_mono
    {α : Type*} (blocks : List (List α)) {i j : Nat}
    (hij : i ≤ j) :
    prefixLength blocks i ≤ prefixLength blocks j := by
  exact ((List.take_isPrefix_take (l := blocks)).2 (Or.inl hij)).flatten.length_le

theorem crossesCut_index_unique
    {α : Type*} (blocks : List (List α)) (cut : Nat)
    {i j : Fin blocks.length}
    (hi : CrossesCut blocks cut i)
    (hj : CrossesCut blocks cut j) :
    i = j := by
  apply Fin.ext
  simp only [CrossesCut] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hmono : prefixLength blocks (i.1 + 1) ≤
        prefixLength blocks j.1 :=
      prefixLength_mono blocks (by omega)
    omega
  · have hmono : prefixLength blocks (j.1 + 1) ≤
        prefixLength blocks i.1 :=
      prefixLength_mono blocks (by omega)
    omega

theorem crossesCut_finset_card_le_one
    {α : Type*} (blocks : List (List α)) (cut : Nat) :
    (Finset.univ.filter fun i : Fin blocks.length =>
      CrossesCut blocks cut i).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact crossesCut_index_unique blocks cut
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

#print axioms prefixLength
#print axioms CrossesCut
#print axioms prefixLength_mono
#print axioms crossesCut_index_unique
#print axioms crossesCut_finset_card_le_one

end FamilyStickyCinematicL32Prop41MarcusTardosPartitionCutUniqueV1
