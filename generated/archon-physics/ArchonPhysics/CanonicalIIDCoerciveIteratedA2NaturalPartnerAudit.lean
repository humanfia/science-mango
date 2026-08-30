import ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge
import ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
import ArchonPhysics.NestedOscillatoryEnergyIdentity

/-!
# Audit of natural actual iterated-A2 partner candidates

This module tests the finite symmetries naturally present in the actual
iterated quadratic second-Picard index: relabelling the two outer tensor
slots, swapping the two inner quadratic children, the established inner
branch/sign twist, charge conjugation, time reversal, and reversal of the two
time layers.

The charge-preserving spatial candidates all leave the *weighted* common-
denominator numerator invariant.  Thus even the candidates which are genuine
fixed-point-free involutions double a nonzero numerator rather than cancel it.
Charge conjugation reverses the Haar charge and therefore is not a partner
inside a nonzero charge fiber.  Time reversal conjugates the weighted
numerator, while order reversal has the exact shuffle-product residual.  No
`O(gamma)` estimate for any of these residuals is assumed.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2NaturalPartnerAudit

open scoped ComplexConjugate Interval

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.NestedOscillatoryEnergyIdentity
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.ModeCoupling
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-! ## Outer-slot relabelling -/

/-- Relabel the two outer tensor slots while moving the distinguished
first-Picard slot with its physical leg. -/
def swapIteratedA2OuterSlots {N : Nat}
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    IteratedQuadraticSecondPicardCharacterTerm N :=
  (iteratedQuadraticOuterModes term ∘ quadraticInputSlotSwap,
    otherQuadraticSlot (iteratedQuadraticFirstPicardSlot term),
    iteratedQuadraticFreeSign term,
    iteratedQuadraticInnerEntry term)

@[simp] theorem swapIteratedA2OuterSlots_firstPicardSlot
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFirstPicardSlot (swapIteratedA2OuterSlots term) =
      otherQuadraticSlot (iteratedQuadraticFirstPicardSlot term) := rfl

@[simp] theorem swapIteratedA2OuterSlots_involutive
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    swapIteratedA2OuterSlots (swapIteratedA2OuterSlots term) = term := by
  rcases term with ⟨modes, slot, freeSign, entry⟩
  apply Prod.ext
  · funext r
    fin_cases r <;> rfl
  · apply Prod.ext
    · fin_cases slot <;> rfl
    · rfl

theorem swapIteratedA2OuterSlots_ne_self
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    swapIteratedA2OuterSlots term ≠ term := by
  intro h
  have hslot := congrArg iteratedQuadraticFirstPicardSlot h
  exact otherQuadraticSlot_ne_self
    (iteratedQuadraticFirstPicardSlot term) hslot

@[simp] theorem swapIteratedA2OuterSlots_firstPicardMode
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFirstPicardMode (swapIteratedA2OuterSlots term) =
      iteratedQuadraticFirstPicardMode term := by
  rcases term with ⟨modes, slot, freeSign, entry⟩
  fin_cases slot <;> rfl

@[simp] theorem swapIteratedA2OuterSlots_freeMode
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeMode (swapIteratedA2OuterSlots term) =
      iteratedQuadraticFreeMode term := by
  rcases term with ⟨modes, slot, freeSign, entry⟩
  fin_cases slot <;> rfl

@[simp] theorem swapIteratedA2OuterSlots_freeCharge
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeCharge (swapIteratedA2OuterSlots term) =
      iteratedQuadraticFreeCharge term := by
  unfold iteratedQuadraticFreeCharge
  rw [swapIteratedA2OuterSlots_freeMode]
  rfl

@[simp] theorem swapIteratedA2OuterSlots_charge
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardCharge (swapIteratedA2OuterSlots term) =
      iteratedQuadraticSecondPicardCharge term := by
  unfold iteratedQuadraticSecondPicardCharge
  rw [swapIteratedA2OuterSlots_freeCharge]
  rfl

@[simp] theorem swapIteratedA2OuterSlots_innerMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticInnerMismatch m (swapIteratedA2OuterSlots term) =
      iteratedQuadraticInnerMismatch m term := by
  unfold iteratedQuadraticInnerMismatch
  rw [swapIteratedA2OuterSlots_firstPicardMode]
  rfl

@[simp] theorem swapIteratedA2OuterSlots_outerMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticOuterMismatch m observed
        (swapIteratedA2OuterSlots term) =
      iteratedQuadraticOuterMismatch m observed term := by
  unfold iteratedQuadraticOuterMismatch
  rw [swapIteratedA2OuterSlots_freeCharge,
    swapIteratedA2OuterSlots_firstPicardMode]
  rfl

@[simp] theorem swapIteratedA2OuterSlots_commute_innerFlip
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    swapIteratedA2OuterSlots (flipIteratedQuadraticInnerBranch term) =
      flipIteratedQuadraticInnerBranch (swapIteratedA2OuterSlots term) := by
  rcases term with ⟨modes, slot, freeSign,
    ⟨⟨innerModes, signZero, signOne⟩, branch⟩⟩
  rfl

theorem iteratedTensor_outerSlotSwap_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    interactionTensor m 3
        (Fin.cons observed
          (iteratedQuadraticOuterModes (swapIteratedA2OuterSlots term))) =
      interactionTensor m 3
        (Fin.cons observed (iteratedQuadraticOuterModes term)) := by
  rw [show
    Fin.cons observed
        (iteratedQuadraticOuterModes (swapIteratedA2OuterSlots term)) =
      Fin.cons observed (iteratedQuadraticOuterModes term) ∘
        quadraticCollisionLegSwap by
      funext r
      fin_cases r <;> rfl]
  exact interactionTensor_perm m _ quadraticCollisionLegSwap

@[simp] theorem swapIteratedA2OuterSlots_staticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed (swapIteratedA2OuterSlots term) =
      iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term := by
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  split_ifs
  · rw [iteratedTensor_outerSlotSwap_eq,
      swapIteratedA2OuterSlots_freeMode,
      swapIteratedA2OuterSlots_firstPicardMode]
    rfl
  · rfl

@[simp] theorem swapIteratedA2OuterSlots_rawNumerator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistCancellationNumerator m observed time
        (swapIteratedA2OuterSlots term) =
      physicalIteratedA2TwistCancellationNumerator
        m observed time term := by
  unfold physicalIteratedA2TwistCancellationNumerator
  rw [swapIteratedA2OuterSlots_outerMismatch,
    swapIteratedA2OuterSlots_innerMismatch,
    ← swapIteratedA2OuterSlots_commute_innerFlip,
    swapIteratedA2OuterSlots_outerMismatch,
    swapIteratedA2OuterSlots_innerMismatch]

@[simp] theorem swapIteratedA2OuterSlots_denominator
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistDenominator m (swapIteratedA2OuterSlots term) =
      physicalIteratedA2TwistDenominator m term := by
  unfold physicalIteratedA2TwistDenominator
  rw [swapIteratedA2OuterSlots_innerMismatch,
    ← swapIteratedA2OuterSlots_commute_innerFlip,
    swapIteratedA2OuterSlots_innerMismatch]

@[simp] theorem swapIteratedA2OuterSlots_weightedNumerator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2WeightedTwistNumerator m kappa radius observed time
        (swapIteratedA2OuterSlots term) =
      physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term := by
  unfold physicalIteratedA2WeightedTwistNumerator
  rw [swapIteratedA2OuterSlots_staticCoefficient,
    swapIteratedA2OuterSlots_rawNumerator]

/-! ## Swap of the two inner quadratic children -/

/-- Exchange the two ordered children of the inner quadratic vertex. -/
def swapIteratedA2InnerChildren {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    IteratedQuadraticSecondPicardCharacterTerm N :=
  (iteratedQuadraticOuterModes term,
    iteratedQuadraticFirstPicardSlot term,
    iteratedQuadraticFreeSign term,
    swapQuadraticPhaseTerm (iteratedQuadraticInnerEntry term).1,
    (iteratedQuadraticInnerEntry term).2)

@[simp] theorem swapIteratedA2InnerChildren_outerModes
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticOuterModes (swapIteratedA2InnerChildren term) =
      iteratedQuadraticOuterModes term := rfl

@[simp] theorem swapIteratedA2InnerChildren_firstPicardSlot
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFirstPicardSlot (swapIteratedA2InnerChildren term) =
      iteratedQuadraticFirstPicardSlot term := rfl

@[simp] theorem swapIteratedA2InnerChildren_freeSign
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeSign (swapIteratedA2InnerChildren term) =
      iteratedQuadraticFreeSign term := rfl

@[simp] theorem swapIteratedA2InnerChildren_innerEntry
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticInnerEntry (swapIteratedA2InnerChildren term) =
      (swapQuadraticPhaseTerm (iteratedQuadraticInnerEntry term).1,
        (iteratedQuadraticInnerEntry term).2) := rfl

@[simp] theorem swapIteratedA2InnerChildren_firstPicardMode
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFirstPicardMode (swapIteratedA2InnerChildren term) =
      iteratedQuadraticFirstPicardMode term := rfl

@[simp] theorem swapIteratedA2InnerChildren_freeMode
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeMode (swapIteratedA2InnerChildren term) =
      iteratedQuadraticFreeMode term := rfl

@[simp] theorem swapIteratedA2InnerChildren_freeCharge
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeCharge (swapIteratedA2InnerChildren term) =
      iteratedQuadraticFreeCharge term := rfl

@[simp] theorem swapIteratedA2InnerChildren_involutive
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    swapIteratedA2InnerChildren (swapIteratedA2InnerChildren term) = term := by
  rcases term with ⟨modes, slot, freeSign, innerTerm, branch⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change (swapQuadraticPhaseTerm (swapQuadraticPhaseTerm innerTerm),
          branch) = (innerTerm, branch)
        rw [swapQuadraticPhaseTerm_involutive]

theorem swapIteratedA2InnerChildren_eq_self_iff
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    swapIteratedA2InnerChildren term = term ↔
      swapQuadraticPhaseTerm (iteratedQuadraticInnerEntry term).1 =
        (iteratedQuadraticInnerEntry term).1 := by
  rcases term with ⟨modes, slot, freeSign, innerTerm, branch⟩
  simp only [swapIteratedA2InnerChildren, iteratedQuadraticOuterModes,
    iteratedQuadraticFirstPicardSlot, iteratedQuadraticFreeSign,
    iteratedQuadraticInnerEntry, Prod.mk.injEq, true_and, and_true]

@[simp] theorem swapIteratedA2InnerChildren_commute_innerFlip
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    swapIteratedA2InnerChildren (flipIteratedQuadraticInnerBranch term) =
      flipIteratedQuadraticInnerBranch (swapIteratedA2InnerChildren term) := by
  rcases term with ⟨modes, slot, freeSign,
    ⟨⟨innerModes, signZero, signOne⟩, branch⟩⟩
  apply Prod.ext rfl
  apply Prod.ext rfl
  apply Prod.ext rfl
  apply Prod.ext
  · apply Prod.ext
    · funext r
      fin_cases r <;> rfl
    · rfl
  · rfl

@[simp] theorem swapIteratedA2InnerChildren_charge
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardCharge (swapIteratedA2InnerChildren term) =
      iteratedQuadraticSecondPicardCharge term := by
  unfold iteratedQuadraticSecondPicardCharge
  rw [swapIteratedA2InnerChildren_freeCharge]
  congr 1
  unfold physlibQuadraticFirstPicardCoordinateCharacterCharge
    twoBranchRealPartCharge
  rw [swapIteratedA2InnerChildren_innerEntry]
  rcases (iteratedQuadraticInnerEntry term).2 with _ | branch
  · simp
  · simp

@[simp] theorem swapIteratedA2InnerChildren_innerMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticInnerMismatch m (swapIteratedA2InnerChildren term) =
      iteratedQuadraticInnerMismatch m term := by
  unfold iteratedQuadraticInnerMismatch firstPicardCoordinateBranchMismatch
  rw [swapIteratedA2InnerChildren_firstPicardMode,
    swapIteratedA2InnerChildren_innerEntry, quadraticPhaseMismatch_swap]

@[simp] theorem swapIteratedA2InnerChildren_outerMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticOuterMismatch m observed
        (swapIteratedA2InnerChildren term) =
      iteratedQuadraticOuterMismatch m observed term := by
  rfl

@[simp] theorem swapIteratedA2InnerChildren_staticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed (swapIteratedA2InnerChildren term) =
      iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term := by
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  split_ifs
  · rw [swapIteratedA2InnerChildren_outerModes,
      swapIteratedA2InnerChildren_freeMode,
      swapIteratedA2InnerChildren_firstPicardMode,
      swapIteratedA2InnerChildren_innerEntry]
    unfold firstPicardCoordinateBranchStaticCoefficient
    split_ifs <;> simp
  · rfl

@[simp] theorem swapIteratedA2InnerChildren_rawNumerator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistCancellationNumerator m observed time
        (swapIteratedA2InnerChildren term) =
      physicalIteratedA2TwistCancellationNumerator
        m observed time term := by
  unfold physicalIteratedA2TwistCancellationNumerator
  rw [swapIteratedA2InnerChildren_outerMismatch,
    swapIteratedA2InnerChildren_innerMismatch,
    ← swapIteratedA2InnerChildren_commute_innerFlip,
    swapIteratedA2InnerChildren_outerMismatch,
    swapIteratedA2InnerChildren_innerMismatch]

@[simp] theorem swapIteratedA2InnerChildren_denominator
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistDenominator m
        (swapIteratedA2InnerChildren term) =
      physicalIteratedA2TwistDenominator m term := by
  unfold physicalIteratedA2TwistDenominator
  rw [swapIteratedA2InnerChildren_innerMismatch,
    ← swapIteratedA2InnerChildren_commute_innerFlip,
    swapIteratedA2InnerChildren_innerMismatch]

@[simp] theorem swapIteratedA2InnerChildren_weightedNumerator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2WeightedTwistNumerator m kappa radius observed time
        (swapIteratedA2InnerChildren term) =
      physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term := by
  unfold physicalIteratedA2WeightedTwistNumerator
  rw [swapIteratedA2InnerChildren_staticCoefficient,
    swapIteratedA2InnerChildren_rawNumerator]


/-! ## Complete finite table of charge-preserving spatial candidates -/

@[simp] theorem swapIteratedA2OuterSlots_commute_innerChildren
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    swapIteratedA2OuterSlots (swapIteratedA2InnerChildren term) =
      swapIteratedA2InnerChildren (swapIteratedA2OuterSlots term) := by
  rcases term with ⟨modes, slot, freeSign,
    ⟨⟨innerModes, signZero, signOne⟩, branch⟩⟩
  rfl

/-- The eight transformations generated by outer relabelling, inner-child
exchange, and the established inner branch/sign twist. -/
inductive IteratedA2NaturalSpatialCandidate where
  | identity
  | outer
  | children
  | twist
  | outerChildren
  | outerTwist
  | childrenTwist
  | outerChildrenTwist
  deriving DecidableEq

/-- Action of a natural spatial candidate on a complete actual history. -/
def IteratedA2NaturalSpatialCandidate.act
    {N : Nat} [NeZero N]
    (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    IteratedQuadraticSecondPicardCharacterTerm N :=
  match candidate with
  | .identity => term
  | .outer => swapIteratedA2OuterSlots term
  | .children => swapIteratedA2InnerChildren term
  | .twist => flipIteratedQuadraticInnerBranch term
  | .outerChildren =>
      swapIteratedA2OuterSlots (swapIteratedA2InnerChildren term)
  | .outerTwist =>
      swapIteratedA2OuterSlots (flipIteratedQuadraticInnerBranch term)
  | .childrenTwist =>
      swapIteratedA2InnerChildren (flipIteratedQuadraticInnerBranch term)
  | .outerChildrenTwist =>
      swapIteratedA2OuterSlots
        (swapIteratedA2InnerChildren
          (flipIteratedQuadraticInnerBranch term))

@[simp] theorem naturalSpatialCandidate_involutive
    {N : Nat} [NeZero N]
    (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    candidate.act (candidate.act term) = term := by
  cases candidate <;>
    simp [IteratedA2NaturalSpatialCandidate.act]

@[simp] theorem naturalSpatialCandidate_charge
    {N : Nat} [NeZero N]
    (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardCharge (candidate.act term) =
      iteratedQuadraticSecondPicardCharge term := by
  cases candidate <;>
    simp [IteratedA2NaturalSpatialCandidate.act]

@[simp] theorem naturalSpatialCandidate_denominator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistDenominator m (candidate.act term) =
      physicalIteratedA2TwistDenominator m term := by
  cases candidate <;>
    simp [IteratedA2NaturalSpatialCandidate.act,
      physicalIteratedA2TwistDenominator_flip_eq]

/-- Sign picked up separately by the raw numerator and static coefficient.
It is negative exactly for candidates containing the established twist. -/
def IteratedA2NaturalSpatialCandidate.parity
    (candidate : IteratedA2NaturalSpatialCandidate) : Complex :=
  match candidate with
  | .identity | .outer | .children | .outerChildren => 1
  | .twist | .outerTwist | .childrenTwist | .outerChildrenTwist => -1

@[simp] theorem naturalSpatialCandidate_rawNumerator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (time : Real) (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistCancellationNumerator m observed time
        (candidate.act term) =
      candidate.parity *
        physicalIteratedA2TwistCancellationNumerator
          m observed time term := by
  cases candidate <;>
    simp [IteratedA2NaturalSpatialCandidate.act,
      IteratedA2NaturalSpatialCandidate.parity,
      physicalIteratedA2TwistCancellationNumerator_flip_eq_neg]

@[simp] theorem naturalSpatialCandidate_staticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
        (candidate.act term) =
      candidate.parity *
        iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term := by
  cases candidate <;>
    simp [IteratedA2NaturalSpatialCandidate.act,
      IteratedA2NaturalSpatialCandidate.parity,
      iteratedQuadraticSecondPicardStaticCoefficient_flip_eq_neg]

@[simp] theorem naturalSpatialCandidate_weightedNumerator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2WeightedTwistNumerator m kappa radius observed time
        (candidate.act term) =
      physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term := by
  cases candidate <;>
    simp [IteratedA2NaturalSpatialCandidate.act,
      physicalIteratedA2WeightedTwistNumerator_flip_eq]

/-- Exact exclusion formula: every natural charge-preserving spatial
candidate doubles the norm of a nonzero weighted numerator. -/
theorem norm_weightedNumerator_add_naturalCandidate_eq_two_mul
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ‖physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term +
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time (candidate.act term)‖ =
      2 * ‖physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term‖ := by
  rw [naturalSpatialCandidate_weightedNumerator, ← two_mul, norm_mul]
  norm_num

theorem weightedNumerator_naturalCandidate_pair_ne_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (candidate : IteratedA2NaturalSpatialCandidate)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hnonzero : physicalIteratedA2WeightedTwistNumerator
      m kappa radius observed time term ≠ 0) :
    physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term +
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time (candidate.act term) ≠ 0 := by
  rw [naturalSpatialCandidate_weightedNumerator]
  intro hsum
  apply hnonzero
  apply mul_left_cancel₀ (show (2 : Complex) ≠ 0 by norm_num)
  simpa only [two_mul, mul_zero] using hsum


/-- The child swap has genuine fixed histories, so it cannot be used as a
global fixed-point-free pairing. -/
theorem swapIteratedA2InnerChildren_has_fixed_history
    {N : Nat} [NeZero N]
    (outerModes : Fin 2 → Lattice.Site N) (slot freeSign branch : Fin 2)
    (mode : Lattice.Site N) (sign : Fin 2) :
    let innerModes : Fin 2 → Lattice.Site N := fun _ => mode
    let term : IteratedQuadraticSecondPicardCharacterTerm N :=
      (outerModes, slot, freeSign, (innerModes, sign, sign), branch)
    swapIteratedA2InnerChildren term = term := by
  dsimp
  apply (swapIteratedA2InnerChildren_eq_self_iff _).2
  exact (swapQuadraticPhaseTerm_eq_self_iff _).2 ⟨rfl, rfl⟩

/-- Apart from identity and the child swap (which has the preceding fixed
histories), every candidate in the finite spatial table is globally
fixed-point-free. -/
theorem naturalSpatialCandidate_identity_or_children_or_fixedPointFree
    {N : Nat} [NeZero N]
    (candidate : IteratedA2NaturalSpatialCandidate) :
    candidate = .identity ∨ candidate = .children ∨
      ∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
        candidate.act term ≠ term := by
  cases candidate with
  | identity => exact Or.inl rfl
  | children => exact Or.inr (Or.inl rfl)
  | outer =>
      right; right; intro term
      exact swapIteratedA2OuterSlots_ne_self term
  | twist =>
      right; right; intro term
      exact flipIteratedQuadraticInnerBranch_ne term
  | outerChildren =>
      right; right; intro term h
      have hslot := congrArg iteratedQuadraticFirstPicardSlot h
      have hbad : otherQuadraticSlot
          (iteratedQuadraticFirstPicardSlot term) =
          iteratedQuadraticFirstPicardSlot term := by
        simpa [IteratedA2NaturalSpatialCandidate.act,
          swapIteratedA2InnerChildren_firstPicardSlot] using hslot
      exact otherQuadraticSlot_ne_self _ hbad
  | outerTwist =>
      right; right; intro term h
      have hslot := congrArg iteratedQuadraticFirstPicardSlot h
      have hbad : otherQuadraticSlot
          (iteratedQuadraticFirstPicardSlot term) =
          iteratedQuadraticFirstPicardSlot term := by
        simpa [IteratedA2NaturalSpatialCandidate.act] using hslot
      exact otherQuadraticSlot_ne_self _ hbad
  | childrenTwist =>
      right; right; intro term h
      have hbranch := congrArg
        (fun t => (iteratedQuadraticInnerEntry t).2) h
      have hbad : otherQuadraticSlot
          (iteratedQuadraticInnerEntry term).2 =
          (iteratedQuadraticInnerEntry term).2 := by
        simpa [IteratedA2NaturalSpatialCandidate.act] using hbranch
      exact otherQuadraticSlot_ne_self _ hbad
  | outerChildrenTwist =>
      right; right; intro term h
      have hslot := congrArg iteratedQuadraticFirstPicardSlot h
      have hbad : otherQuadraticSlot
          (iteratedQuadraticFirstPicardSlot term) =
          iteratedQuadraticFirstPicardSlot term := by
        simpa [IteratedA2NaturalSpatialCandidate.act,
          swapIteratedA2InnerChildren_firstPicardSlot] using hslot
      exact otherQuadraticSlot_ne_self _ hbad

/-! ## Global sign conjugation -/

/-- Reverse the free real-character sign and the reconstructed inner
coordinate branch.  Raw inner quadratic signs are not changed. -/
def conjugateIteratedA2Signs {N : Nat}
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    IteratedQuadraticSecondPicardCharacterTerm N :=
  (iteratedQuadraticOuterModes term,
    iteratedQuadraticFirstPicardSlot term,
    otherQuadraticSlot (iteratedQuadraticFreeSign term),
    (iteratedQuadraticInnerEntry term).1,
    otherQuadraticSlot (iteratedQuadraticInnerEntry term).2)

@[simp] theorem conjugateIteratedA2Signs_outerModes
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticOuterModes (conjugateIteratedA2Signs term) =
      iteratedQuadraticOuterModes term := rfl

@[simp] theorem conjugateIteratedA2Signs_firstPicardSlot
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFirstPicardSlot (conjugateIteratedA2Signs term) =
      iteratedQuadraticFirstPicardSlot term := rfl

@[simp] theorem conjugateIteratedA2Signs_freeSign
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeSign (conjugateIteratedA2Signs term) =
      otherQuadraticSlot (iteratedQuadraticFreeSign term) := rfl

@[simp] theorem conjugateIteratedA2Signs_firstPicardMode
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFirstPicardMode (conjugateIteratedA2Signs term) =
      iteratedQuadraticFirstPicardMode term := rfl

@[simp] theorem conjugateIteratedA2Signs_freeMode
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeMode (conjugateIteratedA2Signs term) =
      iteratedQuadraticFreeMode term := rfl

@[simp] theorem conjugateIteratedA2Signs_involutive
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    conjugateIteratedA2Signs (conjugateIteratedA2Signs term) = term := by
  rcases term with ⟨modes, slot, freeSign, innerTerm, branch⟩
  change (modes, slot, otherQuadraticSlot (otherQuadraticSlot freeSign),
      innerTerm, otherQuadraticSlot (otherQuadraticSlot branch)) =
    (modes, slot, freeSign, innerTerm, branch)
  simp

theorem conjugateIteratedA2Signs_ne_self
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    conjugateIteratedA2Signs term ≠ term := by
  intro h
  have hsign := congrArg iteratedQuadraticFreeSign h
  exact otherQuadraticSlot_ne_self (iteratedQuadraticFreeSign term) hsign

@[simp] theorem conjugateIteratedA2Signs_innerEntry
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticInnerEntry (conjugateIteratedA2Signs term) =
      ((iteratedQuadraticInnerEntry term).1,
        otherQuadraticSlot (iteratedQuadraticInnerEntry term).2) := rfl

@[simp] theorem conjugateIteratedA2Signs_commute_innerFlip
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    conjugateIteratedA2Signs (flipIteratedQuadraticInnerBranch term) =
      flipIteratedQuadraticInnerBranch (conjugateIteratedA2Signs term) := by
  rcases term with ⟨modes, slot, freeSign,
    ⟨innerTerm, branch⟩⟩
  simp [conjugateIteratedA2Signs, flipIteratedQuadraticInnerBranch,
    iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
    iteratedQuadraticFreeSign, iteratedQuadraticInnerEntry]

@[simp] theorem binarySignedMode_charge_other_eq_neg
    {N : Nat} [NeZero N] (mode : Lattice.Site N) (sign : Fin 2) :
    (binarySignedMode mode (otherQuadraticSlot sign)).charge =
      -(binarySignedMode mode sign).charge := by
  fin_cases sign <;>
    simp [binarySignedMode, binaryPhaseSign, SignedMode.charge,
      PhaseSign.exponent, Pi.single_neg]

@[simp] theorem conjugateIteratedA2Signs_freeCharge
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeCharge (conjugateIteratedA2Signs term) =
      -iteratedQuadraticFreeCharge term := by
  unfold iteratedQuadraticFreeCharge
  rw [conjugateIteratedA2Signs_freeMode,
    conjugateIteratedA2Signs_freeSign,
    binarySignedMode_charge_other_eq_neg]

@[simp] theorem conjugateIteratedA2Signs_innerCoordinateCharge
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physlibQuadraticFirstPicardCoordinateCharacterCharge
        (iteratedQuadraticInnerEntry (conjugateIteratedA2Signs term)) =
      -physlibQuadraticFirstPicardCoordinateCharacterCharge
        (iteratedQuadraticInnerEntry term) := by
  rcases term with ⟨modes, slot, freeSign, innerTerm, branch⟩
  fin_cases branch <;>
    simp [conjugateIteratedA2Signs, iteratedQuadraticOuterModes,
      iteratedQuadraticFirstPicardSlot, iteratedQuadraticFreeSign,
      iteratedQuadraticInnerEntry,
      physlibQuadraticFirstPicardCoordinateCharacterCharge,
      twoBranchRealPartCharge]

@[simp] theorem conjugateIteratedA2Signs_charge
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardCharge (conjugateIteratedA2Signs term) =
      -iteratedQuadraticSecondPicardCharge term := by
  unfold iteratedQuadraticSecondPicardCharge
  rw [conjugateIteratedA2Signs_freeCharge,
    conjugateIteratedA2Signs_innerCoordinateCharge]
  abel

@[simp] theorem conjugateIteratedA2Signs_innerMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticInnerMismatch m (conjugateIteratedA2Signs term) =
      -iteratedQuadraticInnerMismatch m term := by
  unfold iteratedQuadraticInnerMismatch firstPicardCoordinateBranchMismatch
  rw [conjugateIteratedA2Signs_firstPicardMode,
    conjugateIteratedA2Signs_innerEntry,
    firstPicardCoordinateBranchSign_other]
  ring

@[simp] theorem conjugateIteratedA2Signs_outerMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticOuterMismatch m observed
        (conjugateIteratedA2Signs term) =
      2 * modeFrequency m observed -
        iteratedQuadraticOuterMismatch m observed term := by
  unfold iteratedQuadraticOuterMismatch
  rw [conjugateIteratedA2Signs_freeCharge, chargeFrequency_neg,
    conjugateIteratedA2Signs_firstPicardMode,
    conjugateIteratedA2Signs_innerEntry,
    firstPicardCoordinateBranchSign_other]
  ring

@[simp] theorem firstPicardStaticCoefficient_flipRawSigns
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved
        (flipQuadraticPhaseTermRawSigns entry.1, entry.2) =
      firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved entry := by
  unfold firstPicardCoordinateBranchStaticCoefficient
  split_ifs <;> simp

@[simp] theorem firstPicardStaticCoefficient_otherBranch_eq_neg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved
        (entry.1, otherQuadraticSlot entry.2) =
      -firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved entry := by
  calc
    firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved
        (entry.1, otherQuadraticSlot entry.2) =
      firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved
        (flipQuadraticPhaseTermRawSigns entry.1,
          otherQuadraticSlot entry.2) :=
          (firstPicardStaticCoefficient_flipRawSigns m kappa radius
            innerObserved (entry.1, otherQuadraticSlot entry.2)).symm
    _ = -firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved entry :=
      firstPicardCoordinateBranchStaticCoefficient_flip_eq_neg
        m kappa radius innerObserved entry

@[simp] theorem conjugateIteratedA2Signs_staticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardStaticCoefficient m kappa radius observed
        (conjugateIteratedA2Signs term) =
      -iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term := by
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  split_ifs
  · rw [conjugateIteratedA2Signs_outerModes,
      conjugateIteratedA2Signs_freeMode,
      conjugateIteratedA2Signs_firstPicardMode,
      conjugateIteratedA2Signs_innerEntry,
      firstPicardStaticCoefficient_otherBranch_eq_neg]
    ring
  · ring

@[simp] theorem conjugateIteratedA2Signs_denominator
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistDenominator m (conjugateIteratedA2Signs term) =
      physicalIteratedA2TwistDenominator m term := by
  unfold physicalIteratedA2TwistDenominator
  rw [conjugateIteratedA2Signs_innerMismatch,
    ← conjugateIteratedA2Signs_commute_innerFlip,
    conjugateIteratedA2Signs_innerMismatch]
  push_cast
  ring

/-- Exact raw-numerator effect of charge conjugation.  The shifted outer
mismatches show why this is neither the raw odd nor the raw even symmetry. -/
theorem conjugateIteratedA2Signs_rawNumerator_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistCancellationNumerator m observed time
        (conjugateIteratedA2Signs term) =
      nestedTwistCancellationNumerator
        (2 * modeFrequency m observed -
          iteratedQuadraticOuterMismatch m observed term)
        (-iteratedQuadraticInnerMismatch m term)
        (2 * modeFrequency m observed -
          iteratedQuadraticOuterMismatch m observed
            (flipIteratedQuadraticInnerBranch term))
        (-iteratedQuadraticInnerMismatch m
          (flipIteratedQuadraticInnerBranch term)) time := by
  unfold physicalIteratedA2TwistCancellationNumerator
  rw [conjugateIteratedA2Signs_outerMismatch,
    conjugateIteratedA2Signs_innerMismatch,
    ← conjugateIteratedA2Signs_commute_innerFlip,
    conjugateIteratedA2Signs_outerMismatch,
    conjugateIteratedA2Signs_innerMismatch]


/-! ## Time reversal and reversal of the two time layers -/

theorem oscillatoryIntegral_time_neg (delta time : Real) :
    oscillatoryIntegral delta (-time) =
      -oscillatoryIntegral (-delta) time := by
  unfold oscillatoryIntegral
  rw [intervalIntegral.integral_symm]
  have hchange :
      (∫ x in -time..0, Complex.exp ((Complex.I * delta) * x)) =
        ∫ x in 0..time,
          Complex.exp ((Complex.I * delta) * (-x)) := by
    symm
    simpa using intervalIntegral.integral_comp_neg
      (a := 0) (b := time)
      (f := fun x : Real => Complex.exp ((Complex.I * delta) * x))
  rw [hchange]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  push_cast
  ring_nf

theorem nestedOscillatoryIntegral_time_neg (outer inner time : Real) :
    nestedOscillatoryIntegral outer inner (-time) =
      nestedOscillatoryIntegral (-outer) (-inner) time := by
  unfold nestedOscillatoryIntegral
  rw [intervalIntegral.integral_symm]
  have hchange :
      (∫ x in -time..0,
          Complex.exp ((Complex.I * outer) * x) *
            oscillatoryIntegral inner x) =
        ∫ x in 0..time,
          Complex.exp ((Complex.I * outer) * (-x)) *
            oscillatoryIntegral inner (-x) := by
    symm
    simpa using intervalIntegral.integral_comp_neg
      (a := 0) (b := time)
      (f := fun x : Real =>
        Complex.exp ((Complex.I * outer) * x) *
          oscillatoryIntegral inner x)
  rw [hchange, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp
  rw [oscillatoryIntegral_time_neg]
  push_cast
  ring_nf

theorem nestedTwistCancellationNumerator_time_neg
    (outer inner outerTwist innerTwist time : Real) :
    nestedTwistCancellationNumerator
        outer inner outerTwist innerTwist (-time) =
      starRingEnd Complex (nestedTwistCancellationNumerator
        outer inner outerTwist innerTwist time) := by
  unfold nestedTwistCancellationNumerator
  simp_rw [oscillatoryIntegral_time_neg,
    ← star_oscillatoryIntegral_eq_neg]
  simp only [map_sub, map_mul]
  simp
  ring

theorem star_iteratedQuadraticSecondPicardStaticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    starRingEnd Complex (iteratedQuadraticSecondPicardStaticCoefficient
      m kappa radius observed term) =
        iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term := by
  apply Complex.ext
  · simp
  · simp [iteratedQuadraticSecondPicardStaticCoefficient_im]

theorem physicalRawNumerator_time_neg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistCancellationNumerator m observed (-time) term =
      starRingEnd Complex
        (physicalIteratedA2TwistCancellationNumerator
          m observed time term) := by
  unfold physicalIteratedA2TwistCancellationNumerator
  exact nestedTwistCancellationNumerator_time_neg _ _ _ _ time

theorem physicalWeightedNumerator_time_neg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed (-time) term =
      starRingEnd Complex (physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term) := by
  unfold physicalIteratedA2WeightedTwistNumerator
  rw [physicalRawNumerator_time_neg, map_mul,
    star_iteratedQuadraticSecondPicardStaticCoefficient]

theorem physicalWeightedNumerator_add_timeReverse_eq_two_re
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term +
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed (-time) term =
      ((2 * (physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term).re : Real) : Complex) := by
  rw [physicalWeightedNumerator_time_neg]
  apply Complex.ext
  · simp
    ring
  · simp

theorem physicalWeightedNumerator_timeReverse_pair_ne_zero_of_re
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hre : (physicalIteratedA2WeightedTwistNumerator
      m kappa radius observed time term).re ≠ 0) :
    physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term +
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed (-time) term ≠ 0 := by
  rw [physicalWeightedNumerator_add_timeReverse_eq_two_re]
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hre)

theorem nestedTwistDifference_add_orderReverse
    (outer inner outerTwist innerTwist time : Real) :
    nestedTwistDifference outer inner outerTwist innerTwist time +
        nestedTwistDifference inner outer innerTwist outerTwist time =
      oscillatoryIntegral outer time * oscillatoryIntegral inner time -
        oscillatoryIntegral outerTwist time *
          oscillatoryIntegral innerTwist time := by
  unfold nestedTwistDifference
  calc
    (nestedOscillatoryIntegral outer inner time -
          nestedOscillatoryIntegral outerTwist innerTwist time) +
        (nestedOscillatoryIntegral inner outer time -
          nestedOscillatoryIntegral innerTwist outerTwist time) =
      (nestedOscillatoryIntegral outer inner time +
          nestedOscillatoryIntegral inner outer time) -
        (nestedOscillatoryIntegral outerTwist innerTwist time +
          nestedOscillatoryIntegral innerTwist outerTwist time) := by ring
    _ = oscillatoryIntegral outer time * oscillatoryIntegral inner time -
        oscillatoryIntegral outerTwist time *
          oscillatoryIntegral innerTwist time := by
      rw [nestedOscillatoryIntegral_add_swap,
        nestedOscillatoryIntegral_add_swap]

private theorem audit_oscillatoryIntegral_one_pi :
    oscillatoryIntegral 1 Real.pi = 2 * Complex.I := by
  rw [oscillatoryIntegral_eq_div (by norm_num)]
  norm_num
  rw [show Complex.I * (Real.pi : Complex) =
      (Real.pi : Complex) * Complex.I by ring]
  rw [Complex.exp_pi_mul_I]
  apply Complex.ext <;> norm_num

private theorem audit_oscillatoryIntegral_neg_one_pi :
    oscillatoryIntegral (-1) Real.pi = -(2 * Complex.I) := by
  rw [← star_oscillatoryIntegral_eq_neg,
    audit_oscillatoryIntegral_one_pi]
  apply Complex.ext <;> norm_num

private theorem audit_exp_three_pi_mul_I :
    Complex.exp (3 * (Real.pi : Complex) * Complex.I) = -1 := by
  rw [show 3 * (Real.pi : Complex) * Complex.I =
      2 * (Real.pi : Complex) * Complex.I +
        (Real.pi : Complex) * Complex.I by ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I,
    Complex.exp_pi_mul_I]
  ring

private theorem audit_oscillatoryIntegral_three_pi :
    oscillatoryIntegral 3 Real.pi =
      (2 / 3 : Real) * Complex.I := by
  rw [oscillatoryIntegral_eq_div (by norm_num)]
  norm_num
  rw [show Complex.I * ((3 : Complex) * (Real.pi : Complex)) =
      3 * (Real.pi : Complex) * Complex.I by ring]
  rw [audit_exp_three_pi_mul_I]
  field_simp [Complex.I_ne_zero]
  simp [Complex.I_sq]
  ring

theorem orderReversal_shuffleResidual_unitGood_ne_zero :
    oscillatoryIntegral 1 Real.pi * oscillatoryIntegral 1 Real.pi -
        oscillatoryIntegral 3 Real.pi *
          oscillatoryIntegral (-1) Real.pi ≠ 0 := by
  rw [audit_oscillatoryIntegral_one_pi,
    audit_oscillatoryIntegral_three_pi,
    audit_oscillatoryIntegral_neg_one_pi]
  intro hzero
  have heval :
      2 * Complex.I * (2 * Complex.I) +
          (2 / 3 : Real) * Complex.I * (2 * Complex.I) =
        ((-16 / 3 : Real) : Complex) := by
    rw [show 2 * Complex.I * (2 * Complex.I) =
        4 * (Complex.I * Complex.I) by ring,
      show ((2 / 3 : Real) : Complex) * Complex.I * (2 * Complex.I) =
        ((4 / 3 : Real) : Complex) *
          (Complex.I * Complex.I) by
          push_cast
          ring,
      Complex.I_mul_I]
    norm_num
  rw [mul_neg, sub_neg_eq_add] at hzero
  rw [heval] at hzero
  norm_num at hzero

theorem orderReversal_unitGood_obstruction :
    NestedTwistGood 1 1 1 3 (-1) ∧
      NestedTwistGood 1 1 1 (-1) 3 ∧
      (1 : Real) + 1 = 3 + (-1) ∧
      (1 : Real) + 1 = (-1) + 3 ∧
      nestedTwistDifference 1 1 3 (-1) Real.pi +
          nestedTwistDifference 1 1 (-1) 3 Real.pi ≠ 0 := by
  refine ⟨by norm_num [NestedTwistGood],
    by norm_num [NestedTwistGood], by norm_num, by norm_num, ?_⟩
  rw [nestedTwistDifference_add_orderReverse]
  exact orderReversal_shuffleResidual_unitGood_ne_zero


end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2NaturalPartnerAudit
