import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosTripleSublistBridgeV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1

/-!
# Triple sublists and cyclic orientation

These are the finite list bridges used by the triple characterization.  They
contain no intersection-reverse or cardinal estimate premise.
-/

/-- Filtering a nodup parent by the support of a literal sublist recovers the
sublist in exactly the same order. -/
theorem filter_toFinset_eq_of_sublist_of_nodup
    {symbol : Type*} [DecidableEq symbol]
    {child parent : List symbol}
    (hsub : child <+ parent) (hparent : parent.Nodup) :
    parent.filter (fun a => a ∈ child.toFinset) = child := by
  induction hsub with
  | slnil => simp
  | cons a hsub ih =>
      rw [List.nodup_cons] at hparent
      have ha : a ∉ _ := fun ha => hparent.1 (hsub.subset ha)
      rw [List.filter_cons_of_neg (by simpa using ha)]
      simpa only [List.mem_toFinset] using ih hparent.2
  | cons_cons a hsub ih =>
      rw [List.nodup_cons] at hparent
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      have hih := ih hparent.2
      simp only [List.mem_toFinset] at hih
      rw [← hih]
      apply List.filter_congr
      intro b hb
      have hba : b ≠ a := fun hba => hparent.1 (hba ▸ hb)
      simp [hba]
      intro hb1
      exact hsub.subset hb1

/-- Restricting a host order to three symbols is unchanged if one first
restricts to a second cyclic sequence containing all three symbols. -/
theorem tripleOrder_eq_commonOrder_filter
    {symbol : Type*} [DecidableEq symbol]
    (host other : DistinctCyclicSequence symbol) (x y z : symbol)
    (hx : x ∈ other.support) (hy : y ∈ other.support)
    (hz : z ∈ other.support) :
    tripleOrder host x y z =
      (host.commonOrder other).filter
        (fun a => a ∈ tripleSupport x y z) := by
  simp only [tripleOrder, commonOrder, List.filter_filter]
  symm
  apply List.filter_congr
  intro a ha
  by_cases htriple : a ∈ tripleSupport x y z
  · have haOther : a ∈ other.support := by
      simp only [tripleSupport, Finset.mem_insert,
        Finset.mem_singleton] at htriple
      rcases htriple with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    simp [htriple, haOther]
  · simp [htriple]

/-- A literal ordered triple in any rotation of the common order has the
same cyclic orientation in the original host sequence. -/
theorem cyclicallyOrdered_of_triple_sublist_rotated_commonOrder
    {symbol : Type*} [DecidableEq symbol]
    (host other : DistinctCyclicSequence symbol)
    {rotated : List symbol} {x y z : symbol}
    (hrot : host.commonOrder other ~r rotated)
    (hsub : [x, y, z] <+ rotated) :
    CyclicallyOrdered host x y z := by
  have hrotNodup : rotated.Nodup :=
    (hrot.nodup_iff).mp (commonOrder_nodup host other)
  have hxRot : x ∈ rotated := hsub.subset (by simp)
  have hyRot : y ∈ rotated := hsub.subset (by simp)
  have hzRot : z ∈ rotated := hsub.subset (by simp)
  have hxCommon : x ∈ host.commonOrder other := hrot.mem_iff.mpr hxRot
  have hyCommon : y ∈ host.commonOrder other := hrot.mem_iff.mpr hyRot
  have hzCommon : z ∈ host.commonOrder other := hrot.mem_iff.mpr hzRot
  have hxOther : x ∈ other.support :=
    (mem_commonOrder_iff host other x).mp hxCommon |>.2
  have hyOther : y ∈ other.support :=
    (mem_commonOrder_iff host other y).mp hyCommon |>.2
  have hzOther : z ∈ other.support :=
    (mem_commonOrder_iff host other z).mp hzCommon |>.2
  have hcommon := tripleOrder_eq_commonOrder_filter
    host other x y z hxOther hyOther hzOther
  have hrotFilter := IsRotated.filterByFinset
    (tripleSupport x y z) hrot
  have hrotatedFilter :
      rotated.filter (fun a => a ∈ tripleSupport x y z) = [x, y, z] := by
    have hfilter := filter_toFinset_eq_of_sublist_of_nodup hsub hrotNodup
    simpa [tripleSupport] using hfilter
  unfold CyclicallyOrdered
  rw [hcommon]
  simpa only [hrotatedFilter] using hrotFilter

#print axioms filter_toFinset_eq_of_sublist_of_nodup
#print axioms tripleOrder_eq_commonOrder_filter
#print axioms cyclicallyOrdered_of_triple_sublist_rotated_commonOrder

end FamilyStickyCinematicL32Prop41MarcusTardosTripleSublistBridgeV1
