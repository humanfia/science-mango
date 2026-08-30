import ArchonPhysics.CanonicalIIDCoerciveIteratedA2NaturalPartnerAudit

/-!
Consumer for the actual iterated-A2 natural partner exclusion table.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped ComplexConjugate

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2NaturalPartnerAudit
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

example {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    swapIteratedA2OuterSlots (swapIteratedA2OuterSlots term) = term ∧
      swapIteratedA2OuterSlots term ≠ term :=
  ⟨swapIteratedA2OuterSlots_involutive term,
    swapIteratedA2OuterSlots_ne_self term⟩

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardCharge (swapIteratedA2OuterSlots term) =
        iteratedQuadraticSecondPicardCharge term ∧
      physicalIteratedA2TwistDenominator m (swapIteratedA2OuterSlots term) =
        physicalIteratedA2TwistDenominator m term ∧
      physicalIteratedA2WeightedTwistNumerator m kappa radius observed time
          (swapIteratedA2OuterSlots term) =
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term := by
  simp

example {N : Nat} [NeZero N]
    (outerModes : Fin 2 → Lattice.Site N) (slot freeSign branch : Fin 2)
    (mode : Lattice.Site N) (sign : Fin 2) :
    let innerModes : Fin 2 → Lattice.Site N := fun _ => mode
    let term : IteratedQuadraticSecondPicardCharacterTerm N :=
      (outerModes, slot, freeSign, (innerModes, sign, sign), branch)
    swapIteratedA2InnerChildren term = term :=
  swapIteratedA2InnerChildren_has_fixed_history
    outerModes slot freeSign branch mode sign

example {N : Nat} [NeZero N]
    (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    candidate.act (candidate.act term) = term ∧
      iteratedQuadraticSecondPicardCharge (candidate.act term) =
        iteratedQuadraticSecondPicardCharge term :=
  ⟨naturalSpatialCandidate_involutive candidate term,
    naturalSpatialCandidate_charge candidate term⟩

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistCancellationNumerator m observed time
          (candidate.act term) =
        candidate.parity *
          physicalIteratedA2TwistCancellationNumerator
            m observed time term ∧
      iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
          (candidate.act term) =
        candidate.parity *
          iteratedQuadraticSecondPicardStaticCoefficient
            m kappa radius observed term ∧
      physicalIteratedA2TwistDenominator m (candidate.act term) =
        physicalIteratedA2TwistDenominator m term ∧
      physicalIteratedA2WeightedTwistNumerator m kappa radius observed time
          (candidate.act term) =
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term := by
  simp

example {N : Nat} [NeZero N]
    (candidate : IteratedA2NaturalSpatialCandidate) :
    candidate = .identity ∨ candidate = .children ∨
      ∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
        candidate.act term ≠ term :=
  naturalSpatialCandidate_identity_or_children_or_fixedPointFree candidate

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ‖physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term +
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time (candidate.act term)‖ =
      2 * ‖physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term‖ :=
  norm_weightedNumerator_add_naturalCandidate_eq_two_mul
    m kappa radius observed time candidate term

example {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    conjugateIteratedA2Signs (conjugateIteratedA2Signs term) = term ∧
      conjugateIteratedA2Signs term ≠ term ∧
      iteratedQuadraticSecondPicardCharge (conjugateIteratedA2Signs term) =
        -iteratedQuadraticSecondPicardCharge term :=
  ⟨conjugateIteratedA2Signs_involutive term,
    conjugateIteratedA2Signs_ne_self term,
    conjugateIteratedA2Signs_charge term⟩

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticInnerMismatch m (conjugateIteratedA2Signs term) =
        -iteratedQuadraticInnerMismatch m term ∧
      iteratedQuadraticOuterMismatch m observed
          (conjugateIteratedA2Signs term) =
        2 * modeFrequency m observed -
          iteratedQuadraticOuterMismatch m observed term ∧
      iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
          (conjugateIteratedA2Signs term) =
        -iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term ∧
      physicalIteratedA2TwistDenominator m (conjugateIteratedA2Signs term) =
        physicalIteratedA2TwistDenominator m term := by
  simp

example (outer inner outerTwist innerTwist time : Real) :
    nestedTwistCancellationNumerator
        outer inner outerTwist innerTwist (-time) =
      starRingEnd Complex (nestedTwistCancellationNumerator
        outer inner outerTwist innerTwist time) :=
  nestedTwistCancellationNumerator_time_neg
    outer inner outerTwist innerTwist time

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed (-time) term =
      starRingEnd Complex (physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term) :=
  physicalWeightedNumerator_time_neg
    m kappa radius observed time term

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hre : (physicalIteratedA2WeightedTwistNumerator
      m kappa radius observed time term).re ≠ 0) :
    physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term +
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed (-time) term ≠ 0 :=
  physicalWeightedNumerator_timeReverse_pair_ne_zero_of_re
    m kappa radius observed time term hre

example (outer inner outerTwist innerTwist time : Real) :
    nestedTwistDifference outer inner outerTwist innerTwist time +
        nestedTwistDifference inner outer innerTwist outerTwist time =
      oscillatoryIntegral outer time * oscillatoryIntegral inner time -
        oscillatoryIntegral outerTwist time *
          oscillatoryIntegral innerTwist time :=
  nestedTwistDifference_add_orderReverse
    outer inner outerTwist innerTwist time

example :
    NestedTwistGood 1 1 1 3 (-1) ∧
      NestedTwistGood 1 1 1 (-1) 3 ∧
      (1 : Real) + 1 = 3 + (-1) ∧
      (1 : Real) + 1 = (-1) + 3 ∧
      nestedTwistDifference 1 1 3 (-1) Real.pi +
          nestedTwistDifference 1 1 (-1) 3 Real.pi ≠ 0 :=
  orderReversal_unitGood_obstruction

end

end ArchonPhysicsConsumers.Thermalization
