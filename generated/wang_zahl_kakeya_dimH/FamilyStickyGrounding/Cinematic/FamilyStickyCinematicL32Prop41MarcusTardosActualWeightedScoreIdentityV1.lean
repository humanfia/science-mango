import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualDyadicLevelScoreCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFourCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveFinalV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualWeightedScoreIdentityV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualDyadicLevelScoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFourCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveFinalV1
open FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1

/-!
# Exact identification of the Lemma 4 score with the Lemma 5 `Q` score
-/

theorem oneLevel_actualScore_eq_sum_actualLevelQ
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B) (level : Fin depth) :
    (∑ p : symbol × symbol,
      dyadicOrderTerm (level.1 + 1) A p *
        dyadicOrderTerm (level.1 + 1) B p) =
      ∑ pair : LeaderPair (depth := depth) A B level,
        actualLevelQ A B hreverse level pair := by
  let C := levelLemmaTwoCertificate A B hreverse (level.1 + 1)
  simpa [actualLevelQ, C] using
    (sum_dyadicOrderTerm_product_eq_sum_dyadicPairQ
      (level.1 + 1) A B C)

theorem actualDyadicPairScore_eq_totalWeightedQ
    {index symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    {depth : Nat} (family : index → DistinctCyclicSequence symbol)
    (weight : Fin depth → Real) (i j : index)
    (hreverse : (family i).IntersectionReverse (family j)) :
    actualDyadicPairScore family weight i j =
      totalWeightedQ weight (actualLevelQ (family i) (family j) hreverse) := by
  classical
  unfold actualDyadicPairScore totalWeightedQ
  apply Finset.sum_congr rfl
  intro level hlevel
  calc
    (∑ p : symbol × symbol,
      weight level * dyadicOrderTerm (level.1 + 1) (family i) p *
        dyadicOrderTerm (level.1 + 1) (family j) p) =
        weight level *
          ∑ p : symbol × symbol,
            dyadicOrderTerm (level.1 + 1) (family i) p *
              dyadicOrderTerm (level.1 + 1) (family j) p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = weight level *
        ∑ pair : LeaderPair (depth := depth) (family i) (family j) level,
          actualLevelQ (family i) (family j) hreverse level pair := by
      rw [oneLevel_actualScore_eq_sum_actualLevelQ
        (family i) (family j) hreverse level]

#print axioms oneLevel_actualScore_eq_sum_actualLevelQ
#print axioms actualDyadicPairScore_eq_totalWeightedQ

end FamilyStickyCinematicL32Prop41MarcusTardosActualWeightedScoreIdentityV1
