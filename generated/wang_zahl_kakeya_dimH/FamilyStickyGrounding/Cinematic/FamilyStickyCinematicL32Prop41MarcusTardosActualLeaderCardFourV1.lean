import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLeaderCardV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicSingularPairV1
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderCardFourV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosCommonPairParentV1
open FamilyStickyCinematicL32Prop41MarcusTardosLeaderCardV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicSingularPairV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1

/-! # At most four actual first-regular leaders at every depth -/

noncomputable def eligibleLeaderPairs
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (level : Fin depth) : Finset (LeaderPair (depth := depth) A B level) := by
  classical
  by_cases hzero : level.1 = 0
  · exact Finset.univ
  · exact leaderChildren (commonPairParent A B)
      (fun parent => ¬dyadicPairSingular level.1 A B parent)
      (fun child => ¬dyadicPairSingular (level.1 + 1) A B child)

theorem eligibleLeaderPairs_card_le_four
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B)
    (level : Fin depth) :
    (eligibleLeaderPairs A B level).card ≤ 4 := by
  classical
  by_cases hzero : level.1 = 0
  · unfold eligibleLeaderPairs
    simp [hzero, LeaderPair, CommonPairIndex]
  · unfold eligibleLeaderPairs
    simp only [hzero, ↓reduceDIte]
    apply leaderChildren_card_le_four
    · have hs := dyadicSingularPairs_card_le_one level.1 A B hreverse
      have heq :
          ((Finset.univ : Finset (CommonPairIndex level.1 A B)).filter
            fun p => dyadicPairSingular level.1 A B p) =
            dyadicSingularPairs level.1 A B := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          mem_dyadicSingularPairs]
        rfl
      have hsing :
          ((Finset.univ : Finset (CommonPairIndex level.1 A B)).filter
            fun p => dyadicPairSingular level.1 A B p).card ≤ 1 := by
        rw [heq]
        exact hs
      simpa only [not_not] using hsing
    · exact commonPairParent_fiber_card_le_four A B

theorem leaderNode_mem_eligibleLeaderPairs
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (x : CommonSymbol A B) :
    (leaderNode depth hdepth A B hlength x).2 ∈
      eligibleLeaderPairs A B (leaderNode depth hdepth A B hlength x).1 := by
  classical
  by_cases hzero : (leaderNode depth hdepth A B hlength x).1.1 = 0
  · simp [eligibleLeaderPairs, hzero]
  · have hpositive : 0 < (leaderNode depth hdepth A B hlength x).1.1 :=
      Nat.pos_of_ne_zero hzero
    have hreg := leaderNode_regular depth hdepth A B hlength x
    have hparent := leaderNode_parent_singular
      depth hdepth A B hlength x hpositive
    simpa [eligibleLeaderPairs, hzero, leaderChildren] using
      And.intro hreg hparent

theorem actualLeaders_fixedLevel_card_le_four
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (hreverse : A.IntersectionReverse B)
    (level : Fin depth) :
    ((actualLeaders depth hdepth A B hlength).filter
      fun node => node.1 = level).card ≤ 4 := by
  classical
  let ambient : Finset (Sigma (LeaderPair (depth := depth) A B)) :=
    ({level} : Finset (Fin depth)).sigma (eligibleLeaderPairs A B)
  have hsub :
      (actualLeaders depth hdepth A B hlength).filter
          (fun node => node.1 = level) ⊆ ambient := by
    intro node hnode
    have hparts := Finset.mem_filter.mp hnode
    rw [actualLeaders, Finset.mem_image] at hparts
    obtain ⟨x, hx, rfl⟩ := hparts.1
    simp only [ambient, Finset.mem_sigma, Finset.mem_singleton]
    exact ⟨hparts.2, leaderNode_mem_eligibleLeaderPairs
      depth hdepth A B hlength x⟩
  calc
    ((actualLeaders depth hdepth A B hlength).filter
        fun node => node.1 = level).card ≤ ambient.card :=
      Finset.card_le_card hsub
    _ = (eligibleLeaderPairs A B level).card := by
      simp [ambient]
    _ ≤ 4 := eligibleLeaderPairs_card_le_four A B hreverse level

#print axioms eligibleLeaderPairs
#print axioms eligibleLeaderPairs_card_le_four
#print axioms leaderNode_mem_eligibleLeaderPairs
#print axioms actualLeaders_fixedLevel_card_le_four

end FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderCardFourV1
