import ArchonPhysics.ThreeSignedChargeCancellationClassification

/-!
# Consumer: three-leg cancellation in a matched iterated tree

This consumer exposes the exact finite charge classification used by a
free-initial/iterated-second-Picard interference term.  It retains ordered
placements, repeated modes, and the all-equal case.  In particular, the
classification does not assert a unique observed leg when modes coincide.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- Three signed unit charges returning a prescribed positive unit charge
have two positive legs and one negative leg, with the positive modes equal as
an unordered pair to the observed and negative-leg modes. -/
theorem problem_three_signedMode_charge_eq_positive_classification
    {d : Type*} [Finite d] [DecidableEq d]
    (observed : d) (leg₀ leg₁ leg₂ : SignedMode d)
    (hcharge : leg₀.charge + leg₁.charge + leg₂.charge =
      (positiveSignedMode observed).charge) :
    (leg₀.sign = .phase ∧ leg₁.sign = .phase ∧
        leg₂.sign = .conjugate ∧
        PositivePairMatchesObservedCancel observed
          leg₀.mode leg₁.mode leg₂.mode) ∨
      (leg₀.sign = .phase ∧ leg₁.sign = .conjugate ∧
        leg₂.sign = .phase ∧
        PositivePairMatchesObservedCancel observed
          leg₀.mode leg₂.mode leg₁.mode) ∨
      (leg₀.sign = .conjugate ∧ leg₁.sign = .phase ∧
        leg₂.sign = .phase ∧
        PositivePairMatchesObservedCancel observed
          leg₁.mode leg₂.mode leg₀.mode) :=
  three_signedMode_charge_eq_positive_classification
    observed leg₀ leg₁ leg₂ hcharge

/-- The positive/conjugate coordinate branch is represented by leaving or
flipping both binary signs of the two inner legs. -/
theorem problem_physlibFirstPicardCoordinateCharge_eq_adjustedInnerLegs
    {N : Nat} [NeZero N]
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    physlibQuadraticFirstPicardCoordinateCharacterCharge entry =
      (adjustedFirstPicardInnerLeg entry 0).charge +
        (adjustedFirstPicardInnerLeg entry 1).charge :=
  physlibFirstPicardCoordinateCharge_eq_adjustedInnerLegs entry

/-- The full charge of an iterated-quadratic tree is the charge of its free
leg plus the charges of its two branch-adjusted inner legs. -/
theorem problem_iteratedQuadraticSecondPicardCharge_eq_threeLegs
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardCharge term =
      (iteratedQuadraticFreeSignedLeg term).charge +
        (adjustedFirstPicardInnerLeg
            (iteratedQuadraticInnerEntry term) 0).charge +
        (adjustedFirstPicardInnerLeg
            (iteratedQuadraticInnerEntry term) 1).charge :=
  iteratedQuadraticSecondPicardCharge_eq_threeLegs term

/-- In a free-initial charge-matched iterated tree, some positive leg is an
observed-mode copy and the other positive mode equals the negative-leg mode.
All three ordered sign placements are retained, without choosing a unique
observed copy when modes coincide. -/
theorem problem_matchedIteratedQuadratic_threeLeg_classification
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    let freeLeg := iteratedQuadraticFreeSignedLeg term
    let inner₀ := adjustedFirstPicardInnerLeg
      (iteratedQuadraticInnerEntry term) 0
    let inner₁ := adjustedFirstPicardInnerLeg
      (iteratedQuadraticInnerEntry term) 1
    (freeLeg.sign = .phase ∧ inner₀.sign = .phase ∧
        inner₁.sign = .conjugate ∧
        PositivePairMatchesObservedCancel observed
          freeLeg.mode inner₀.mode inner₁.mode) ∨
      (freeLeg.sign = .phase ∧ inner₀.sign = .conjugate ∧
        inner₁.sign = .phase ∧
        PositivePairMatchesObservedCancel observed
          freeLeg.mode inner₁.mode inner₀.mode) ∨
      (freeLeg.sign = .conjugate ∧ inner₀.sign = .phase ∧
        inner₁.sign = .phase ∧
        PositivePairMatchesObservedCancel observed
          inner₀.mode inner₁.mode freeLeg.mode) :=
  matchedIteratedQuadratic_threeLeg_classification observed term hcharge

#print axioms problem_three_signedMode_charge_eq_positive_classification
#print axioms problem_physlibFirstPicardCoordinateCharge_eq_adjustedInnerLegs
#print axioms problem_iteratedQuadraticSecondPicardCharge_eq_threeLegs
#print axioms problem_matchedIteratedQuadratic_threeLeg_classification

end

end ArchonPhysicsConsumers.Thermalization
