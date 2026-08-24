import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSplitTagScoreCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSublistRankSignTransportV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosBlockPairQCoreV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosBlockPairActualScoreV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosSplitTagScoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosSublistRankSignTransportV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairSplitCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairQCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-!
# One actual block-pair score equals the tagged Marcus--Tardos `Q`

The two ambient list orders may contain symbols outside the common split.
Rank-sign transport along nodup sublists removes them.  The remaining literal
left/right common-symbol lists are then relabeled by `SplitTagScoreCleanV1`.
-/

theorem blockPairActualScore_eq_blockPairQ
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    {ambientA ambientB u v C D : List symbol}
    (hAmbientA : ambientA.Nodup) (hAmbientB : ambientB.Nodup)
    (huv : (u ++ v).Nodup)
    (hCommonA : u ++ v <+ ambientA)
    (hCommonB : u.reverse ++ v.reverse <+ ambientB)
    (hC : C <+ u ++ v) (hD : D <+ u.reverse ++ v.reverse)
    (hCnodup : C.Nodup) (hDnodup : D.Nodup) :
    (∑ a : {x : symbol //
        x ∈ leftCommon u C D ++ rightCommon v C D},
      ∑ b : {x : symbol //
          x ∈ leftCommon u C D ++ rightCommon v C D},
        rankSign (fun x ↦ ambientA.idxOf x) a.1 b.1 *
          rankSign (fun x ↦ ambientB.idxOf x) a.1 b.1) =
      blockPairQ u v C D := by
  let left := leftCommon u C D
  let right := rightCommon v C D
  have hfirst := first_commonOrder_eq_split huv hC hCnodup hDnodup
  have hsecond := second_commonOrder_eq_split_reverse
    huv hD hCnodup hDnodup
  have hleftRightSubC : left ++ right <+ C := by
    rw [← hfirst]
    exact List.filter_sublist
  have hleftRightSubAmbientA : left ++ right <+ ambientA :=
    (hleftRightSubC.trans hC).trans hCommonA
  have hreverseSubD : left.reverse ++ right.reverse <+ D := by
    rw [← hsecond]
    exact List.filter_sublist
  have hreverseSubAmbientB : left.reverse ++ right.reverse <+ ambientB :=
    (hreverseSubD.trans hD).trans hCommonB
  have hleftRightNodup : (left ++ right).Nodup :=
    hleftRightSubAmbientA.nodup hAmbientA
  calc
    (∑ a : {x : symbol // x ∈ left ++ right},
      ∑ b : {x : symbol // x ∈ left ++ right},
        rankSign (fun x ↦ ambientA.idxOf x) a.1 b.1 *
          rankSign (fun x ↦ ambientB.idxOf x) a.1 b.1) =
        ∑ a : {x : symbol // x ∈ left ++ right},
          ∑ b : {x : symbol // x ∈ left ++ right},
            rankSign (fun x ↦ (left ++ right).idxOf x) a.1 b.1 *
              rankSign (fun x ↦
                (left.reverse ++ right.reverse).idxOf x) a.1 b.1 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      have haRev : a.1 ∈ left.reverse ++ right.reverse := by
        simpa using a.2
      have hbRev : b.1 ∈ left.reverse ++ right.reverse := by
        simpa using b.2
      rw [rankSign_idxOf_eq_of_sublist hleftRightSubAmbientA
          hAmbientA a.2 b.2,
        rankSign_idxOf_eq_of_sublist hreverseSubAmbientB
          hAmbientB haRev hbRev]
    _ = taggedSplitQ left.length right.length :=
      sum_actual_split_rank_product_eq_taggedSplitQ
        left right hleftRightNodup
    _ = blockPairQ u v C D := rfl

#print axioms blockPairActualScore_eq_blockPairQ

end FamilyStickyCinematicL32Prop41MarcusTardosBlockPairActualScoreV1
