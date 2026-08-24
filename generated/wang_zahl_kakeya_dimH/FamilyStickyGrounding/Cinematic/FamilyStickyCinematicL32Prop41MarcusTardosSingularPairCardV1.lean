import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosSingularPairCardV1

open FamilyStickyCinematicL32Prop41MarcusTardosPartitionCutUniqueV1
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1

/-!
# At most one singular block pair

Each singular pair crosses the fixed cut in both position-indexed block
partitions.  Cut-crossing indices are unique on each side, so the singular
pair itself is unique.  This is the cardinal part of Marcus--Tardos Lemma 2.
-/

theorem singularPair_unique
    {α : Type*} [DecidableEq α]
    {blocksA blocksB : List (List α)} {u v : List α}
    (hflatA : blocksA.flatten = u ++ v)
    (hflatB : blocksB.flatten = u.reverse ++ v.reverse)
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    {ij kl : Fin blocksA.length × Fin blocksB.length}
    (hij : SingularPair blocksA blocksB hA hB ij)
    (hkl : SingularPair blocksA blocksB hA hB kl) :
    ij = kl := by
  have hi := crossesCut_index_unique blocksA u.length
    (singularPair_crosses_left hflatA hflatB hA hB ij hij)
    (singularPair_crosses_left hflatA hflatB hA hB kl hkl)
  have hj := crossesCut_index_unique blocksB u.length
    (singularPair_crosses_right hflatA hflatB hA hB ij hij)
    (singularPair_crosses_right hflatA hflatB hA hB kl hkl)
  exact Prod.ext hi hj

noncomputable def singularPairs
    {α : Type*} [DecidableEq α]
    (blocksA blocksB : List (List α))
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup) :
    Finset (Fin blocksA.length × Fin blocksB.length) := by
  classical
  exact Finset.univ.filter fun ij => SingularPair blocksA blocksB hA hB ij

@[simp]
theorem mem_singularPairs
    {α : Type*} [DecidableEq α]
    {blocksA blocksB : List (List α)}
    {hA : blocksA.flatten.Nodup} {hB : blocksB.flatten.Nodup}
    (ij : Fin blocksA.length × Fin blocksB.length) :
    ij ∈ singularPairs blocksA blocksB hA hB ↔
      SingularPair blocksA blocksB hA hB ij := by
  classical
  simp [singularPairs]

theorem singularPairs_card_le_one
    {α : Type*} [DecidableEq α]
    {blocksA blocksB : List (List α)} {u v : List α}
    (hflatA : blocksA.flatten = u ++ v)
    (hflatB : blocksB.flatten = u.reverse ++ v.reverse)
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup) :
    (singularPairs blocksA blocksB hA hB).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro ij hij kl hkl
  exact singularPair_unique hflatA hflatB hA hB
    (mem_singularPairs ij |>.mp hij) (mem_singularPairs kl |>.mp hkl)

#print axioms singularPair_unique
#print axioms singularPairs
#print axioms mem_singularPairs
#print axioms singularPairs_card_le_one

end FamilyStickyCinematicL32Prop41MarcusTardosSingularPairCardV1
