import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderCardFourV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosOccurrencePairCardFiberV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderNodeCodeV1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderFibreV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderCardFourV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderNodeCodeV1
open FamilyStickyCinematicL32Prop41MarcusTardosCommonPairParentV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceDyadicRegularityV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrencePairCardFiberV1
open FamilyStickyCinematicL32Prop41MarcusTardosUniqueLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderPathV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1

/-! # A leader-pair fibre is exactly the fibre of the leader-node map -/

noncomputable def leaderNodeFiber
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (node : Sigma (LeaderPair (depth := depth) A B)) :
    Finset (CommonSymbol A B) := by
  classical
  exact Finset.univ.filter fun x =>
    leaderNode depth hdepth A B hlength x = node

theorem leaderNode_eq_of_occurrence_pair_eq
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (node : Sigma (LeaderPair (depth := depth) A B))
    (hnode : node ∈ actualLeaders depth hdepth A B hlength)
    (y : CommonSymbol A B)
    (hpair : occurrenceCommonPairIndex (node.1.1 + 1) A B y.1 y.2 = node.2) :
    leaderNode depth hdepth A B hlength y = node := by
  classical
  have himage := hnode
  rw [actualLeaders, Finset.mem_image] at himage
  obtain ⟨x, hx, hxeq⟩ := himage
  subst node
  let level := (leaderNode depth hdepth A B hlength x).1
  have hyRegular :
      occurrenceRegular A.order B.order A.nodup_order B.nodup_order y.1
        ((A.mem_support_iff y.1).mp (Finset.mem_inter.mp y.2).1)
        ((B.mem_support_iff y.1).mp (Finset.mem_inter.mp y.2).2)
        (level.1 + 1) := by
    apply (not_dyadicPairSingular_occurrence_iff
      (level.1 + 1) A B y.1 y.2).1
    rw [hpair]
    exact leaderNode_regular depth hdepth A B hlength x
  have hyLeader : IsLeaderLevel
      (occurrenceRegular A.order B.order A.nodup_order B.nodup_order y.1
        ((A.mem_support_iff y.1).mp (Finset.mem_inter.mp y.2).1)
        ((B.mem_support_iff y.1).mp (Finset.mem_inter.mp y.2).2))
      (level.1 + 1) := by
    refine ⟨by omega, hyRegular, ?_⟩
    by_cases hzero : level.1 = 0
    · exact Or.inl (by omega)
    · right
      intro hyParentRegular
      have hparentNotSingular :=
        (not_dyadicPairSingular_occurrence_iff
          level.1 A B y.1 y.2).2 hyParentRegular
      apply hparentNotSingular
      have hparentSingular := leaderNode_parent_singular
        depth hdepth A B hlength x (Nat.pos_of_ne_zero hzero)
      have hparentEq :
          occurrenceCommonPairIndex level.1 A B y.1 y.2 =
            commonPairParent A B (leaderNode depth hdepth A B hlength x).2 := by
        calc
          occurrenceCommonPairIndex level.1 A B y.1 y.2 =
              commonPairParent A B
                (occurrenceCommonPairIndex (level.1 + 1) A B y.1 y.2) :=
            (commonPairParent_occurrence A B y.1 y.2).symm
          _ = commonPairParent A B
                (leaderNode depth hdepth A B hlength x).2 := by
            rw [hpair]
      rw [hparentEq]
      exact hparentSingular
  have hyUnique := exists_unique_occurrenceLeader
    A.order B.order A.nodup_order B.nodup_order y.1
    ((A.mem_support_iff y.1).mp (Finset.mem_inter.mp y.2).1)
    ((B.mem_support_iff y.1).mp (Finset.mem_inter.mp y.2).2)
    depth hdepth hlength
  have hyChosen := occurrenceLeaderLevel_spec
    depth hdepth A B hlength y
  have hyCandidate : level.1 + 1 ≤ depth ∧ IsLeaderLevel
      (occurrenceRegular A.order B.order A.nodup_order B.nodup_order y.1
        ((A.mem_support_iff y.1).mp (Finset.mem_inter.mp y.2).1)
        ((B.mem_support_iff y.1).mp (Finset.mem_inter.mp y.2).2))
      (level.1 + 1) := ⟨by omega, hyLeader⟩
  have hlevel : occurrenceLeaderLevel depth hdepth A B hlength y =
      level.1 + 1 := hyUnique.unique hyChosen hyCandidate
  have hfin : leaderLevelFin depth hdepth A B hlength y = level := by
    apply Fin.ext
    simp only [leaderLevelFin]
    omega
  have hv1 := congrArg (fun p => p.1.1) hpair
  have hv2 := congrArg (fun p => p.2.1) hpair
  apply leaderNodeCode_injective A B
  apply Prod.ext
  · exact congrArg Fin.val hfin
  · apply Prod.ext
    · dsimp only [leaderNodeCode, leaderNode]
      rw [congrArg Fin.val hfin]
      exact hv1
    · dsimp only [leaderNodeCode, leaderNode]
      rw [congrArg Fin.val hfin]
      exact hv2

theorem leaderNodeFiber_eq_occurrencePairFiber
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (node : Sigma (LeaderPair (depth := depth) A B))
    (hnode : node ∈ actualLeaders depth hdepth A B hlength) :
    leaderNodeFiber depth hdepth A B hlength node =
      occurrencePairFiber (node.1.1 + 1) A B node.2 := by
  classical
  ext y
  constructor
  · intro hy
    have heq := (Finset.mem_filter.mp hy).2
    cases heq
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, rfl⟩
  · intro hy
    have hpair := (Finset.mem_filter.mp hy).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      leaderNode_eq_of_occurrence_pair_eq
        depth hdepth A B hlength node hnode y hpair⟩

theorem leaderNodeFiber_card_eq_dyadicPairLength
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth)
    (node : Sigma (LeaderPair (depth := depth) A B))
    (hnode : node ∈ actualLeaders depth hdepth A B hlength) :
    (leaderNodeFiber depth hdepth A B hlength node).card =
      dyadicPairLength (node.1.1 + 1) A B node.2 := by
  rw [leaderNodeFiber_eq_occurrencePairFiber
    depth hdepth A B hlength node hnode]
  exact occurrencePairFiber_card_eq_dyadicPairLength
    (node.1.1 + 1) A B node.2

#print axioms leaderNodeFiber
#print axioms leaderNode_eq_of_occurrence_pair_eq
#print axioms leaderNodeFiber_eq_occurrencePairFiber
#print axioms leaderNodeFiber_card_eq_dyadicPairLength

end FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderFibreV1
