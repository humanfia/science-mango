import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceDyadicRegularityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCommonPairParentV1
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderPathV1
open FamilyStickyCinematicL32Prop41MarcusTardosUniqueLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceDyadicRegularityV1
open FamilyStickyCinematicL32Prop41MarcusTardosCommonPairParentV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1

/-! # Actual first-regular leader node of every common symbol -/

abbrev CommonSymbol
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol) :=
  {x : symbol // x ∈ A.support ∩ B.support}

abbrev LeaderPair
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (level : Fin depth) :=
  CommonPairIndex (level.1 + 1) A B

noncomputable def occurrenceLeaderLevel
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (x : CommonSymbol A B) : Nat :=
  Classical.choose <| exists_unique_occurrenceLeader
    A.order B.order A.nodup_order B.nodup_order x.1
    ((A.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).1)
    ((B.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).2)
    depth hdepth hlength

theorem occurrenceLeaderLevel_spec
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (x : CommonSymbol A B) :
    occurrenceLeaderLevel depth hdepth A B hlength x ≤ depth ∧
      IsLeaderLevel
        (occurrenceRegular A.order B.order A.nodup_order B.nodup_order x.1
          ((A.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).1)
          ((B.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).2))
        (occurrenceLeaderLevel depth hdepth A B hlength x) :=
  (Classical.choose_spec <| exists_unique_occurrenceLeader
    A.order B.order A.nodup_order B.nodup_order x.1
    ((A.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).1)
    ((B.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).2)
    depth hdepth hlength).1

noncomputable def leaderLevelFin
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (x : CommonSymbol A B) : Fin depth :=
  ⟨occurrenceLeaderLevel depth hdepth A B hlength x - 1, by
    have hs := occurrenceLeaderLevel_spec depth hdepth A B hlength x
    have hone := hs.2.1
    omega⟩

theorem leaderLevelFin_succ
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (x : CommonSymbol A B) :
    (leaderLevelFin depth hdepth A B hlength x).1 + 1 =
      occurrenceLeaderLevel depth hdepth A B hlength x := by
  have hs := occurrenceLeaderLevel_spec depth hdepth A B hlength x
  have hone := hs.2.1
  simp only [leaderLevelFin]
  omega

noncomputable def leaderNode
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (x : CommonSymbol A B) : Sigma (LeaderPair (depth := depth) A B) :=
  ⟨leaderLevelFin depth hdepth A B hlength x,
    occurrenceCommonPairIndex
      ((leaderLevelFin depth hdepth A B hlength x).1 + 1) A B x.1 x.2⟩

noncomputable def actualLeaders
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth) :
    Finset (Sigma (LeaderPair (depth := depth) A B)) := by
  classical
  exact (A.support ∩ B.support).attach.image
    (leaderNode depth hdepth A B hlength)

theorem leaderNode_regular
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (x : CommonSymbol A B) :
    ¬dyadicPairSingular
      ((leaderNode depth hdepth A B hlength x).1.1 + 1) A B
      (leaderNode depth hdepth A B hlength x).2 := by
  have hs := occurrenceLeaderLevel_spec depth hdepth A B hlength x
  have hreg := hs.2.2.1
  apply (not_dyadicPairSingular_occurrence_iff
    ((leaderLevelFin depth hdepth A B hlength x).1 + 1) A B x.1 x.2).2
  simpa [leaderNode, leaderLevelFin_succ depth hdepth A B hlength x] using hreg

theorem leaderNode_parent_singular
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (x : CommonSymbol A B)
    (hpositive : 0 < (leaderNode depth hdepth A B hlength x).1.1) :
    dyadicPairSingular (leaderNode depth hdepth A B hlength x).1.1 A B
      (commonPairParent A B (leaderNode depth hdepth A B hlength x).2) := by
  have hs := occurrenceLeaderLevel_spec depth hdepth A B hlength x
  have hnot : ¬occurrenceRegular A.order B.order A.nodup_order B.nodup_order x.1
      ((A.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).1)
      ((B.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).2)
      (leaderLevelFin depth hdepth A B hlength x).1 := by
    rcases hs.2.2.2 with hone | hprev
    · simp only [leaderNode] at hpositive
      have hsucc := leaderLevelFin_succ depth hdepth A B hlength x
      omega
    · change ¬occurrenceRegular A.order B.order A.nodup_order B.nodup_order x.1
        ((A.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).1)
        ((B.mem_support_iff x.1).mp (Finset.mem_inter.mp x.2).2)
        (occurrenceLeaderLevel depth hdepth A B hlength x - 1)
      exact hprev
  rw [show commonPairParent A B (leaderNode depth hdepth A B hlength x).2 =
      occurrenceCommonPairIndex
        (leaderLevelFin depth hdepth A B hlength x).1 A B x.1 x.2 by
    exact commonPairParent_occurrence A B x.1 x.2]
  by_contra hregularPair
  exact hnot <| (not_dyadicPairSingular_occurrence_iff
    (leaderLevelFin depth hdepth A B hlength x).1 A B x.1 x.2).1 hregularPair

theorem actualLeaders_regular
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (node : Sigma (LeaderPair (depth := depth) A B))
    (hnode : node ∈ actualLeaders depth hdepth A B hlength) :
    ¬dyadicPairSingular (node.1.1 + 1) A B node.2 := by
  classical
  rw [actualLeaders, Finset.mem_image] at hnode
  obtain ⟨x, hx, rfl⟩ := hnode
  exact leaderNode_regular depth hdepth A B hlength x

#print axioms CommonSymbol
#print axioms LeaderPair
#print axioms occurrenceLeaderLevel
#print axioms occurrenceLeaderLevel_spec
#print axioms leaderLevelFin
#print axioms leaderLevelFin_succ
#print axioms leaderNode
#print axioms actualLeaders
#print axioms leaderNode_regular
#print axioms leaderNode_parent_singular
#print axioms actualLeaders_regular

end FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
