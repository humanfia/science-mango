import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderMassPartitionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderCardFourV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveFinalV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderCardFourV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderMassPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
open FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1
open FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedCoreV1

/-! # Fully actual denominator-free Marcus--Tardos Lemma 5 -/

noncomputable def levelLemmaTwoCertificate
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B)
    (level : Nat) : DyadicLemmaTwoCertificate level A B :=
  Classical.choice (exists_dyadicLemmaTwoCertificate level A B hreverse)

noncomputable def actualLevelQ
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B)
    (level : Fin depth) (pair : LeaderPair (depth := depth) A B level) : Real :=
  let C := levelLemmaTwoCertificate A B hreverse (level.1 + 1)
  dyadicPairQ (level.1 + 1) A B C.left C.right pair

def actualLevelMass
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (level : Fin depth) (pair : LeaderPair (depth := depth) A B level) : Real :=
  dyadicPairLength (level.1 + 1) A B pair

def actualLevelSingular
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (level : Fin depth) (pair : LeaderPair (depth := depth) A B level) : Prop :=
  dyadicPairSingular (level.1 + 1) A B pair

theorem actualLemmaFive_denominatorFree
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B)
    (hlength : A.order.length ≤ 2 ^ depth)
    (weight : Fin depth → Real) (hweight : ∀ level, 0 < weight level) :
    totalWeightedQ weight (actualLevelQ A B hreverse) +
        leaderWeightedSquare (actualLeaders depth hdepth A B hlength)
          weight (actualLevelMass A B) ≤
      ((A.commonOrder B).length : Real) * ∑ level, weight level ∧
    ((A.commonOrder B).length : Real) ^ 2 ≤
      4 * (∑ level, (weight level)⁻¹) *
        leaderWeightedSquare (actualLeaders depth hdepth A B hlength)
          weight (actualLevelMass A B) := by
  classical
  refine lemmaFive_denominatorFree
    weight (actualLevelQ A B hreverse) (actualLevelMass A B)
    (actualLevelSingular A B) ((A.commonOrder B).length : Real)
    (actualLeaders depth hdepth A B hlength) hweight ?_ ?_ ?_ ?_
  · intro level
    let C := levelLemmaTwoCertificate A B hreverse (level.1 + 1)
    have hmass : actualLevelMass A B level =
        (fun pair => (dyadicPairLength (level.1 + 1) A B pair : Real)) := rfl
    have hsing : actualLevelSingular A B level =
        dyadicPairSingular (level.1 + 1) A B := rfl
    rw [hmass, hsing]
    simpa [actualLevelQ, C] using C.qSumBound
  · intro node hnode
    exact actualLeaders_regular depth hdepth A B hlength node hnode
  · exact actualLeaders_fixedLevel_card_le_four
      depth hdepth A B hlength hreverse
  · exact actualLeaderMass_eq_commonOrderLength
      depth hdepth A B hlength

#print axioms levelLemmaTwoCertificate
#print axioms actualLevelQ
#print axioms actualLevelMass
#print axioms actualLevelSingular
#print axioms actualLemmaFive_denominatorFree

end FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveFinalV1
