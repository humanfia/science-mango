import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTripleLinearOrderV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicSmallIntersectionV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosTripleCharacterizationV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosTripleSublistBridgeV1
open FamilyStickyCinematicL32Prop41MarcusTardosTripleLinearOrderV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicSmallIntersectionV1

/-!
# No equally oriented common triple forces opposite cyclic order

This discharges the previously named pure finite core in the five-curve
Marcus--Tardos reduction.  The proof rotates the second common order to the
head of the first one and reconstructs the reversed tail from its literal
two-element sublists.
-/

/-- The complete finite cyclic triple characterization. -/
theorem noSameCyclicTriple_implies_intersectionReverse
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol)
    (hno : NoSameCyclicTriple A B) :
    IntersectionReverse A B := by
  classical
  cases hcommon : A.commonOrder B with
  | nil =>
      apply intersectionReverse_of_common_card_le_two A B
      have hzero : (A.support ∩ B.support).card = 0 := by
        rw [← commonOrder_length A B, hcommon]
        rfl
      omega
  | cons x xs =>
      have hlNodup : (x :: xs).Nodup := by
        simpa only [hcommon] using commonOrder_nodup A B
      have hxCommon : x ∈ A.commonOrder B := by
        rw [hcommon]
        exact List.mem_cons_self
      have hxSupports := (mem_commonOrder_iff A B x).mp hxCommon
      have hxOtherCommon : x ∈ B.commonOrder A :=
        (mem_commonOrder_iff B A x).mpr ⟨hxSupports.2, hxSupports.1⟩
      let anchorIndex := (B.commonOrder A).idxOf x
      let rotated := (B.commonOrder A).rotate anchorIndex
      have hanchorIndex : anchorIndex < (B.commonOrder A).length := by
        exact List.idxOf_lt_length_of_mem hxOtherCommon
      have hhead : rotated.head? = some x := by
        rw [show rotated = (B.commonOrder A).rotate anchorIndex by rfl,
          List.head?_rotate hanchorIndex,
          List.getElem?_idxOf hxOtherCommon]
      cases hrotated : rotated with
      | nil => simp [hrotated] at hhead
      | cons y ys =>
          have hyx : y = x := by
            simpa [hrotated] using hhead
          subst y
          have hrot : B.commonOrder A ~r x :: ys := by
            have hbase : B.commonOrder A ~r rotated :=
              (List.IsRotated.forall (B.commonOrder A) anchorIndex).symm
            simpa only [hrotated] using hbase
          have hrNodup : (x :: ys).Nodup :=
            (hrot.nodup_iff).mp (commonOrder_nodup B A)
          have htailPerm : xs ~ ys := by
            have hfullPerm : A.commonOrder B ~ B.commonOrder A :=
              (List.perm_ext_iff_of_nodup
                (commonOrder_nodup A B) (commonOrder_nodup B A)).mpr (by
                  intro a
                  simp only [mem_commonOrder_iff]
                  tauto)
            have hconsPerm : (x :: xs) ~ (x :: ys) := by
              rw [← hcommon]
              exact hfullPerm.trans hrot.perm
            exact hconsPerm.cons_inv
          have hreversePerm : xs.reverse ~ ys :=
            xs.reverse_perm.trans htailPerm
          have horder : ∀ {a b}, [a, b] <+ ys -> [a, b] <+ xs.reverse := by
            intro a b habYS
            have haYS : a ∈ ys := habYS.subset (by simp)
            have hbYS : b ∈ ys := habYS.subset (by simp)
            have habNe : a ≠ b := by
              have hpairNodup : ([a, b] : List symbol).Nodup :=
                hrNodup.sublist (habYS.cons x)
              simpa using hpairNodup
            have haReverse : a ∈ xs.reverse := hreversePerm.mem_iff.mpr haYS
            have hbReverse : b ∈ xs.reverse := hreversePerm.mem_iff.mpr hbYS
            rcases pair_sublist_or_swap_of_mem_of_ne
                haReverse hbReverse habNe with hab | hba
            · exact hab
            · exfalso
              have habXS : [a, b] <+ xs := by
                simpa using hba.reverse
              have htripleA : [x, a, b] <+ A.commonOrder B := by
                rw [hcommon]
                exact habXS.cons_cons x
              have hcyclicA : CyclicallyOrdered A x a b :=
                cyclicallyOrdered_of_triple_sublist_rotated_commonOrder
                  A B (List.IsRotated.refl _) htripleA
              have htripleB : [x, a, b] <+ x :: ys :=
                habYS.cons_cons x
              have hcyclicB : CyclicallyOrdered B x a b :=
                cyclicallyOrdered_of_triple_sublist_rotated_commonOrder
                  B A hrot htripleB
              have hxNotYS : x ∉ ys := (List.nodup_cons.mp hrNodup).1
              have hxa : x ≠ a := fun hxa => hxNotYS (hxa ▸ haYS)
              have hbx : b ≠ x := fun hbx => hxNotYS (hbx ▸ hbYS)
              have haCommon : a ∈ A.commonOrder B := by
                rw [hcommon]
                exact List.mem_cons_of_mem x (by
                  have : a ∈ xs.reverse := haReverse
                  simpa using this)
              have hbCommon : b ∈ A.commonOrder B := by
                rw [hcommon]
                exact List.mem_cons_of_mem x (by
                  have : b ∈ xs.reverse := hbReverse
                  simpa using this)
              exact hno ⟨x, a, b, hxa, habNe, hbx,
                Finset.mem_inter.mpr hxSupports,
                Finset.mem_inter.mpr
                  ((mem_commonOrder_iff A B a).mp haCommon),
                Finset.mem_inter.mpr
                  ((mem_commonOrder_iff A B b).mp hbCommon),
                hcyclicA, hcyclicB⟩
          have htailEq : xs.reverse = ys :=
            eq_of_perm_of_pair_sublist
              (List.nodup_reverse.mpr (List.nodup_cons.mp hlNodup).2)
              hreversePerm horder
          unfold IntersectionReverse
          rw [hcommon, List.reverse_cons, htailEq]
          exact (List.isRotated_concat x ys).trans hrot.symm

/-- The named producer value replacing the unresolved interface field. -/
theorem tripleCharacterizationCore
    (symbol : Type*) [DecidableEq symbol] :
    TripleCharacterizationCore symbol where
  noSame_implies_intersectionReverse :=
    noSameCyclicTriple_implies_intersectionReverse

#print axioms noSameCyclicTriple_implies_intersectionReverse
#print axioms tripleCharacterizationCore

end FamilyStickyCinematicL32Prop41MarcusTardosTripleCharacterizationV1
