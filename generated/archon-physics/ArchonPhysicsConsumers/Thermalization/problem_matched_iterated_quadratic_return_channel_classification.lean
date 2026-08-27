import ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification

/-!
# Consumer: six matched iterated-quadratic return channels
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

theorem problem_matchedIteratedQuadratic_six_return_channels
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    FreeObservedInnerZeroCancelsInnerOne observed term ∨
      InnerZeroObservedFreeCancelsInnerOne observed term ∨
      FreeObservedInnerOneCancelsInnerZero observed term ∨
      InnerOneObservedFreeCancelsInnerZero observed term ∨
      InnerZeroObservedInnerOneCancelsFree observed term ∨
      InnerOneObservedInnerZeroCancelsFree observed term :=
  matchedIteratedQuadratic_six_return_channels observed term hcharge

theorem problem_matchedIteratedQuadratic_tadpole_or_connected
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    MatchedIteratedQuadraticTadpoleChannel observed term ∨
      MatchedIteratedQuadraticConnectedChannel observed term :=
  matchedIteratedQuadratic_tadpole_or_connected observed term hcharge

#print axioms problem_matchedIteratedQuadratic_six_return_channels
#print axioms problem_matchedIteratedQuadratic_tadpole_or_connected

end

end ArchonPhysicsConsumers.Thermalization
