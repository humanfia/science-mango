import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderFibreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderMassPartitionV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderFibreV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
open FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1

/-! # Exact partition of common-symbol mass by actual leader pairs -/

theorem sum_actualLeader_dyadicPairLength_eq_commonCard
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth) :
    (∑ node ∈ actualLeaders depth hdepth A B hlength,
      dyadicPairLength (node.1.1 + 1) A B node.2) =
      (A.support ∩ B.support).card := by
  classical
  have hfib := Finset.card_eq_sum_card_image
    (leaderNode depth hdepth A B hlength)
    (Finset.univ : Finset (CommonSymbol A B))
  have hsumFiber :
      (∑ node ∈ actualLeaders depth hdepth A B hlength,
        (leaderNodeFiber depth hdepth A B hlength node).card) =
        Fintype.card (CommonSymbol A B) := by
    simpa [actualLeaders, leaderNodeFiber] using hfib.symm
  calc
    (∑ node ∈ actualLeaders depth hdepth A B hlength,
        dyadicPairLength (node.1.1 + 1) A B node.2) =
        ∑ node ∈ actualLeaders depth hdepth A B hlength,
          (leaderNodeFiber depth hdepth A B hlength node).card := by
      apply Finset.sum_congr rfl
      intro node hnode
      exact (leaderNodeFiber_card_eq_dyadicPairLength
        depth hdepth A B hlength node hnode).symm
    _ = Fintype.card (CommonSymbol A B) := hsumFiber
    _ = (A.support ∩ B.support).card := by
      exact Fintype.card_coe _

theorem sum_actualLeader_dyadicPairLength_real_eq_commonOrderLength
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth) :
    (∑ node ∈ actualLeaders depth hdepth A B hlength,
      (dyadicPairLength (node.1.1 + 1) A B node.2 : Real)) =
      ((A.commonOrder B).length : Real) := by
  norm_cast
  rw [sum_actualLeader_dyadicPairLength_eq_commonCard]
  exact (commonOrder_length A B).symm

theorem actualLeaderMass_eq_commonOrderLength
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hlength : A.order.length ≤ 2 ^ depth) :
    leaderMass (actualLeaders depth hdepth A B hlength)
      (fun level pair =>
        (dyadicPairLength (level.1 + 1) A B pair : Real)) =
      ((A.commonOrder B).length : Real) := by
  exact sum_actualLeader_dyadicPairLength_real_eq_commonOrderLength
    depth hdepth A B hlength

#print axioms sum_actualLeader_dyadicPairLength_eq_commonCard
#print axioms sum_actualLeader_dyadicPairLength_real_eq_commonOrderLength
#print axioms actualLeaderMass_eq_commonOrderLength

end FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderMassPartitionV1
