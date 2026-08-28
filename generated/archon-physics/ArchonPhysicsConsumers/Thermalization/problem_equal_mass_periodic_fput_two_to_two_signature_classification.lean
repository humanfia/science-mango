import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoSignatureClassification

/-!
# Consumer: nondegenerate 2-to-2 matched-couple classification

The contracts below expose the exact reduction of presented matched
four-wave couples to two independent two-leg permutations.  No assertion is
made for the explicitly named classification remainder.
-/

namespace ArchonPhysicsConsumers.Thermalization.EqualMassPeriodicFPUTTwoToTwoSignatureClassification

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveHaarPhaseCouples
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoSignatureClassification
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

/-- Abstract nondegenerate `2 ↔ 2` signatures agree exactly under separate
positive-pair and negative-pair permutations. -/
theorem nondegenerateTwoToTwo_signatureClassification_contract
    {Mode : Type*} [DecidableEq Mode]
    (left right : NondegenerateTwoToTwoLegs Mode) :
    twoToTwoPhaseSignature left = twoToTwoPhaseSignature right ↔
      IsTwoToTwoLegPermutation left right := by
  exact twoToTwoPhaseSignature_eq_iff_legPermutation left right

/-- For actual presented effective diagrams, equality of the Haar external
signatures forces one of the four independent pair-swap combinations. -/
theorem actualMatchedTwoToTwo_implies_legPermutation_contract
    {N : Nat} [NeZero N]
    {left right : ActiveEffectiveFourWaveDiagram N}
    (leftPresentation : ExternalTwoToTwoPresentation left.1)
    (rightPresentation : ExternalTwoToTwoPresentation right.1)
    (hmatched : externalFourWavePhaseSignature left.1 =
      externalFourWavePhaseSignature right.1) :
    IsTwoToTwoLegPermutation leftPresentation.legs
      rightPresentation.legs := by
  exact
    (externalFourWavePhaseSignature_eq_iff_twoToTwoLegPermutation
      leftPresentation rightPresentation).1 hmatched

/-- Conversely, any of those four leg permutations gives exact Haar
signature matching. -/
theorem actualLegPermutation_implies_matchedTwoToTwo_contract
    {N : Nat} [NeZero N]
    {left right : ActiveEffectiveFourWaveDiagram N}
    (leftPresentation : ExternalTwoToTwoPresentation left.1)
    (rightPresentation : ExternalTwoToTwoPresentation right.1)
    (hperm : IsTwoToTwoLegPermutation leftPresentation.legs
      rightPresentation.legs) :
    externalFourWavePhaseSignature left.1 =
      externalFourWavePhaseSignature right.1 := by
  exact
    (externalFourWavePhaseSignature_eq_iff_twoToTwoLegPermutation
      leftPresentation rightPresentation).2 hperm

/-- The existing binary-tree matched-couple predicate has the same exact
four-permutation classification on the presented sector. -/
theorem actualTwoToTwo_leafPhaseBalanced_contract
    {N : Nat} [NeZero N]
    {left right : ActiveEffectiveFourWaveDiagram N}
    (leftPresentation : ExternalTwoToTwoPresentation left.1)
    (rightPresentation : ExternalTwoToTwoPresentation right.1) :
    leafPhaseBalanced
        (externalFourWaveDiagramCouple left.1 right.1) ↔
      IsTwoToTwoLegPermutation leftPresentation.legs
        rightPresentation.legs := by
  exact leafPhaseBalanced_iff_twoToTwoLegPermutation
    leftPresentation rightPresentation

/-- Every actual active diagram is routed explicitly either to the strict
nondegenerate `2 ↔ 2` classification or to its transparent remainder. -/
theorem actualDiagram_classified_or_remainder_contract
    {N : Nat} [NeZero N]
    (diagram : ActiveEffectiveFourWaveDiagram N) :
    HasNondegenerateTwoToTwoPresentation diagram.1 ∨
      IsTwoToTwoClassificationRemainder diagram.1 := by
  exact nondegenerateTwoToTwo_or_classificationRemainder diagram.1

/-- Every actual matched active pair is routed either to an explicit
four-permutation classification or to the named matched remainder. -/
theorem actualMatchedPair_classifiedPermutation_or_remainder_contract
    {N : Nat} [NeZero N]
    (left right : ActiveEffectiveFourWaveDiagram N)
    (hmatched : leafPhaseBalanced
      (externalFourWaveDiagramCouple left.1 right.1)) :
    (∃ (leftPresentation : ExternalTwoToTwoPresentation left.1)
        (rightPresentation : ExternalTwoToTwoPresentation right.1),
      IsTwoToTwoLegPermutation leftPresentation.legs
        rightPresentation.legs) ∨
      IsMatchedTwoToTwoClassificationRemainder left.1 right.1 := by
  exact matchedCouple_classifiedPermutation_or_remainder
    left.1 right.1 hmatched

#print axioms nondegenerateTwoToTwo_signatureClassification_contract
#print axioms actualMatchedTwoToTwo_implies_legPermutation_contract
#print axioms actualLegPermutation_implies_matchedTwoToTwo_contract
#print axioms actualTwoToTwo_leafPhaseBalanced_contract
#print axioms actualDiagram_classified_or_remainder_contract
#print axioms actualMatchedPair_classifiedPermutation_or_remainder_contract
#print axioms externalFourWavePhaseSignature_eq_iff_twoToTwoLegPermutation

end

end ArchonPhysicsConsumers.Thermalization.EqualMassPeriodicFPUTTwoToTwoSignatureClassification
