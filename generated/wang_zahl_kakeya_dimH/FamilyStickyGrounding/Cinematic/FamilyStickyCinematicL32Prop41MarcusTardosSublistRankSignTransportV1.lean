import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSublistRankCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosSublistRankSignTransportV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosSublistRankCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-! # Order-sign transport from a nodup list to a sublist -/

theorem rankSign_idxOf_eq_of_sublist
    {symbol : Type*} [DecidableEq symbol]
    {small large : List symbol} (hsub : small <+ large)
    (hlarge : large.Nodup) {a b : symbol}
    (ha : a ∈ small) (hb : b ∈ small) :
    rankSign (fun x ↦ small.idxOf x) a b =
      rankSign (fun x ↦ large.idxOf x) a b := by
  by_cases hab : a = b
  · simp [rankSign, hab]
  · simp only [rankSign, hab, if_false]
    have hiff := idxOf_lt_iff_of_nodup_sublist hsub hlarge ha hb
    by_cases hlt : small.idxOf a < small.idxOf b
    · have hltLarge : large.idxOf a < large.idxOf b := hiff.mp hlt
      simp [hlt, hltLarge]
    · have hltLarge : ¬ large.idxOf a < large.idxOf b := fun h ↦
        hlt (hiff.mpr h)
      simp [hlt, hltLarge]

#print axioms rankSign_idxOf_eq_of_sublist

end FamilyStickyCinematicL32Prop41MarcusTardosSublistRankSignTransportV1
