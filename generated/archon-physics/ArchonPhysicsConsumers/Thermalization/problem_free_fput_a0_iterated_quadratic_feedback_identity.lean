import ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity

/-!
# Consumer: charge-matched A0/iterated-A2 feedback

This consumer exposes the exact return-mismatch and finite-time norm-square
identities on the iterated-quadratic branch of the complete second-Picard
family.  The matched family retains every ordered tree and every repeated-mode
term.  The result identifies the one-step oscillatory norm-square factor; it
does not identify the remaining static weights with a completed macroscopic
gain formula.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-- Matching the singleton free charge on a complete `Sum.inl` term forces
the two nested mismatches to be exact negatives. -/
theorem problem_completeInl_outerMismatch_eq_neg_inner
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    iteratedQuadraticOuterMismatch m observed term =
      -iteratedQuadraticInnerMismatch m term :=
  iteratedQuadraticOuterMismatch_eq_neg_inner_of_completeCharge
    m observed term hcharge

/-- Consumer endpoint for the exact termwise feedback/norm-square identity. -/
theorem problem_freeInitial_completeInl_termwiseFeedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    2 * (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (completeSecondPicardCoefficient
            m kappa beta radius observed time (Sum.inl term))).re =
      iteratedQuadraticFeedbackNormSqTerm
        m kappa time radius observed term :=
  two_mul_re_freeInitial_mul_star_completeInlCoefficient_eq_feedback
    m kappa beta time radius observed term hcharge

/-- Consumer endpoint for the unquotiented finite sum over all matching
ordered iterated trees. -/
theorem problem_freeInitial_completeInl_interference_eq_feedbackSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    equalChargeFamilyInterference
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
          completeSecondPicardCoefficient
            m kappa beta radius observed time (Sum.inl term))
        (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
          completeSecondPicardCharge (Sum.inl term)) =
      ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        if freeInitialPhaseCharge observed 0 =
            completeSecondPicardCharge (Sum.inl term) then
          iteratedQuadraticFeedbackNormSqTerm
            m kappa time radius observed term
        else 0 :=
  equalChargeFamilyInterference_freeInitial_completeInl_eq_feedbackSum
    m kappa beta time radius observed

/-- Equivalent subtype-indexed form of the matched feedback sum. -/
theorem problem_freeInitial_completeInl_interference_eq_matchedSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    equalChargeFamilyInterference
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
          completeSecondPicardCoefficient
            m kappa beta radius observed time (Sum.inl term))
        (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
          completeSecondPicardCharge (Sum.inl term)) =
      ∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
        iteratedQuadraticFeedbackNormSqTerm
          m kappa time radius observed term.1 :=
  equalChargeFamilyInterference_freeInitial_completeInl_eq_matchedSum
    m kappa beta time radius observed

#print axioms problem_completeInl_outerMismatch_eq_neg_inner
#print axioms problem_freeInitial_completeInl_termwiseFeedback
#print axioms problem_freeInitial_completeInl_interference_eq_feedbackSum
#print axioms problem_freeInitial_completeInl_interference_eq_matchedSum

end

end ArchonPhysicsConsumers.Thermalization
