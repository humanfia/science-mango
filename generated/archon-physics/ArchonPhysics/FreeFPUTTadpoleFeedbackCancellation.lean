import ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
import ArchonPhysics.ResonanceWeightSinc

/-!
# Exact cancellation of the two canonical tadpole feedback fibers

We pair tadpole return trees by flipping the real-coordinate branch and both
raw binary signs of the inner quadratic term.  The adjusted signed inner legs
are unchanged, so the matched charge, inner carrier, positive-inner filter,
and canonical return-channel label are all preserved.  The compact static
weight changes sign.

The inner mismatch is not invariant under this involution for a general
tree.  On a tadpole channel, however, the two adjusted inner legs have the
same mode and opposite signs.  Their charge is zero, and the two mismatches
are negatives of one another.  Evenness of the finite-time resonance weight
then makes the full summand antisymmetric.

Cancellation is performed on the disjoint canonical priority fibers for
channels one and three.  No raw overlapping-channel filters are summed, so
all-equal overlap with connected predicates is assigned only once.
-/

namespace ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ResonanceWeightSinc
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- Flip both raw binary signs of a quadratic phase term, leaving its two
ordered modes fixed. -/
def flipQuadraticPhaseTermRawSigns
    {N : Nat} (term : QuadraticPhaseTerm N) : QuadraticPhaseTerm N :=
  (term.1, otherQuadraticSlot term.2.1,
    otherQuadraticSlot term.2.2)

/-- Flip the inner coordinate branch and both raw signs.  All outer data and
all inner modes are left fixed. -/
def flipIteratedQuadraticInnerBranch
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    IteratedQuadraticSecondPicardCharacterTerm N :=
  (iteratedQuadraticOuterModes term,
    iteratedQuadraticFirstPicardSlot term,
    iteratedQuadraticFreeSign term,
    flipQuadraticPhaseTermRawSigns (iteratedQuadraticInnerEntry term).1,
    otherQuadraticSlot (iteratedQuadraticInnerEntry term).2)

@[simp] theorem otherQuadraticSlot_involutive (slot : Fin 2) :
    otherQuadraticSlot (otherQuadraticSlot slot) = slot := by
  fin_cases slot <;> rfl

@[simp] theorem firstPicardCoordinateBranchSign_other (branch : Fin 2) :
    firstPicardCoordinateBranchSign (otherQuadraticSlot branch) =
      -firstPicardCoordinateBranchSign branch := by
  fin_cases branch <;> norm_num

theorem otherQuadraticSlot_ne_self (slot : Fin 2) :
    otherQuadraticSlot slot ≠ slot := by
  fin_cases slot <;> decide

@[simp] theorem flipQuadraticPhaseTermRawSigns_involutive
    {N : Nat} (term : QuadraticPhaseTerm N) :
    flipQuadraticPhaseTermRawSigns
        (flipQuadraticPhaseTermRawSigns term) = term := by
  rcases term with ⟨modes, signZero, signOne⟩
  simp [flipQuadraticPhaseTermRawSigns]

@[simp] theorem flipIteratedQuadraticInnerBranch_involutive
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    flipIteratedQuadraticInnerBranch
        (flipIteratedQuadraticInnerBranch term) = term := by
  rcases term with ⟨outerModes, outerSlot, freeSign,
    ⟨⟨innerModes, signZero, signOne⟩, branch⟩⟩
  simp [flipIteratedQuadraticInnerBranch,
    flipQuadraticPhaseTermRawSigns,
    iteratedQuadraticOuterModes,
    iteratedQuadraticFirstPicardSlot,
    iteratedQuadraticFreeSign,
    iteratedQuadraticInnerEntry]

@[simp] theorem flipIteratedQuadraticInnerBranch_outerModes
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticOuterModes (flipIteratedQuadraticInnerBranch term) =
      iteratedQuadraticOuterModes term := rfl

@[simp] theorem flipIteratedQuadraticInnerBranch_firstPicardSlot
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFirstPicardSlot
        (flipIteratedQuadraticInnerBranch term) =
      iteratedQuadraticFirstPicardSlot term := rfl

@[simp] theorem flipIteratedQuadraticInnerBranch_freeSign
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeSign (flipIteratedQuadraticInnerBranch term) =
      iteratedQuadraticFreeSign term := rfl

@[simp] theorem flipIteratedQuadraticInnerBranch_innerEntry
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticInnerEntry (flipIteratedQuadraticInnerBranch term) =
      (flipQuadraticPhaseTermRawSigns
          (iteratedQuadraticInnerEntry term).1,
        otherQuadraticSlot (iteratedQuadraticInnerEntry term).2) := rfl

@[simp] theorem flipIteratedQuadraticInnerBranch_firstPicardMode
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFirstPicardMode
        (flipIteratedQuadraticInnerBranch term) =
      iteratedQuadraticFirstPicardMode term := rfl

@[simp] theorem flipIteratedQuadraticInnerBranch_freeMode
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeMode (flipIteratedQuadraticInnerBranch term) =
      iteratedQuadraticFreeMode term := rfl

/-- Simultaneously flipping the branch and raw sign leaves each adjusted
inner signed leg literally unchanged. -/
@[simp] theorem adjustedFirstPicardInnerLeg_flipIteratedQuadraticInnerBranch
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) (input : Fin 2) :
    adjustedFirstPicardInnerLeg
        (iteratedQuadraticInnerEntry
          (flipIteratedQuadraticInnerBranch term)) input =
      adjustedFirstPicardInnerLeg
        (iteratedQuadraticInnerEntry term) input := by
  rcases term with ⟨outerModes, outerSlot, freeSign,
    ⟨⟨innerModes, signZero, signOne⟩, branch⟩⟩
  fin_cases input <;> fin_cases branch <;>
    fin_cases signZero <;> fin_cases signOne <;>
    simp [flipIteratedQuadraticInnerBranch,
      flipQuadraticPhaseTermRawSigns,
      iteratedQuadraticOuterModes,
      iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticFreeSign,
      iteratedQuadraticInnerEntry,
      adjustedFirstPicardInnerLeg,
      quadraticPhaseTermBinarySign,
      coordinateBranchAdjustedBinarySign,
      otherQuadraticSlot]

/-- The free signed outer leg is unaffected. -/
@[simp] theorem iteratedQuadraticFreeSignedLeg_flipIteratedQuadraticInnerBranch
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFreeSignedLeg
        (flipIteratedQuadraticInnerBranch term) =
      iteratedQuadraticFreeSignedLeg term := rfl

/-- The reconstructed coordinate-branch charge is preserved. -/
@[simp] theorem physlibFirstPicardCoordinateCharge_flipIteratedQuadraticInnerBranch
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physlibQuadraticFirstPicardCoordinateCharacterCharge
        (iteratedQuadraticInnerEntry
          (flipIteratedQuadraticInnerBranch term)) =
      physlibQuadraticFirstPicardCoordinateCharacterCharge
        (iteratedQuadraticInnerEntry term) := by
  rw [physlibFirstPicardCoordinateCharge_eq_adjustedInnerLegs,
    physlibFirstPicardCoordinateCharge_eq_adjustedInnerLegs,
    adjustedFirstPicardInnerLeg_flipIteratedQuadraticInnerBranch,
    adjustedFirstPicardInnerLeg_flipIteratedQuadraticInnerBranch]

/-- Consequently the complete iterated-tree phase charge is preserved. -/
@[simp] theorem iteratedQuadraticSecondPicardCharge_flipIteratedQuadraticInnerBranch
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardCharge
        (flipIteratedQuadraticInnerBranch term) =
      iteratedQuadraticSecondPicardCharge term := by
  rw [iteratedQuadraticSecondPicardCharge_eq_threeLegs,
    iteratedQuadraticSecondPicardCharge_eq_threeLegs,
    iteratedQuadraticFreeSignedLeg_flipIteratedQuadraticInnerBranch,
    adjustedFirstPicardInnerLeg_flipIteratedQuadraticInnerBranch,
    adjustedFirstPicardInnerLeg_flipIteratedQuadraticInnerBranch]

/-- Positive-inner membership is invariant because the carrier is fixed. -/
@[simp] theorem positiveInner_flipIteratedQuadraticInnerBranch_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    0 < modeFrequency m
        (iteratedQuadraticFirstPicardMode
          (flipIteratedQuadraticInnerBranch term)) ↔
      0 < modeFrequency m (iteratedQuadraticFirstPicardMode term) := by
  rw [flipIteratedQuadraticInnerBranch_firstPicardMode]

/-- Every one of the six raw return predicates depends only on the three
adjusted signed legs, and is therefore invariant under the flip. -/
@[simp] theorem CanonicalReturnChannel.rawHolds_flip_iff
    {N : Nat} [NeZero N] (channel : CanonicalReturnChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    channel.RawHolds observed
        (flipIteratedQuadraticInnerBranch term) ↔
      channel.RawHolds observed term := by
  cases channel <;>
    simp only [CanonicalReturnChannel.RawHolds,
      FreeObservedInnerZeroCancelsInnerOne,
      InnerZeroObservedFreeCancelsInnerOne,
      FreeObservedInnerOneCancelsInnerZero,
      InnerOneObservedFreeCancelsInnerZero,
      InnerZeroObservedInnerOneCancelsFree,
      InnerOneObservedInnerZeroCancelsFree,
      iteratedQuadraticFreeSignedLeg_flipIteratedQuadraticInnerBranch,
      adjustedFirstPicardInnerLeg_flipIteratedQuadraticInnerBranch]

/-- The disjointized priority predicates, including all of their negative
earlier-channel guards, are invariant under the flip. -/
@[simp] theorem CanonicalReturnChannel.priorityHolds_flip_iff
    {N : Nat} [NeZero N] (channel : CanonicalReturnChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    channel.PriorityHolds observed
        (flipIteratedQuadraticInnerBranch term) ↔
      channel.PriorityHolds observed term := by
  cases channel <;>
    simp only [CanonicalReturnChannel.PriorityHolds,
      CanonicalReturnChannel.rawHolds_flip_iff]

/-- The flip restricted to the charge-matched subtype. -/
def flipMatchedIteratedQuadraticInnerBranch
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    FreeInitialMatchedIteratedQuadraticTerm N observed :=
  ⟨flipIteratedQuadraticInnerBranch term.1, by
    simpa only [completeSecondPicardCharge_inl,
      iteratedQuadraticSecondPicardCharge_flipIteratedQuadraticInnerBranch]
      using term.2⟩

@[simp] theorem flipMatchedIteratedQuadraticInnerBranch_coe
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    (flipMatchedIteratedQuadraticInnerBranch observed term).1 =
      flipIteratedQuadraticInnerBranch term.1 := rfl

@[simp] theorem flipMatchedIteratedQuadraticInnerBranch_involutive
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    flipMatchedIteratedQuadraticInnerBranch observed
        (flipMatchedIteratedQuadraticInnerBranch observed term) = term := by
  apply Subtype.ext
  exact flipIteratedQuadraticInnerBranch_involutive term.1

/-- The matched-tree flip as a genuine self-equivalence. -/
def flipMatchedIteratedQuadraticInnerBranchEquiv
    {N : Nat} [NeZero N] (observed : Lattice.Site N) :
    FreeInitialMatchedIteratedQuadraticTerm N observed ≃
      FreeInitialMatchedIteratedQuadraticTerm N observed where
  toFun := flipMatchedIteratedQuadraticInnerBranch observed
  invFun := flipMatchedIteratedQuadraticInnerBranch observed
  left_inv := flipMatchedIteratedQuadraticInnerBranch_involutive observed
  right_inv := flipMatchedIteratedQuadraticInnerBranch_involutive observed

/-- The first-match label is invariant, not merely its underlying raw
predicate.  Hence the all-equal priority assignment is preserved. -/
@[simp] theorem canonicalReturnChannel_flipMatchedIteratedQuadraticInnerBranch
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    canonicalReturnChannel observed
        (flipMatchedIteratedQuadraticInnerBranch observed term) =
      canonicalReturnChannel observed term := by
  apply (canonicalReturnChannel_eq_iff_priorityHolds observed
    (flipMatchedIteratedQuadraticInnerBranch observed term)
    (canonicalReturnChannel observed term)).2
  change (canonicalReturnChannel observed term).PriorityHolds observed
    (flipIteratedQuadraticInnerBranch term.1)
  rw [CanonicalReturnChannel.priorityHolds_flip_iff]
  exact (canonicalReturnChannel_eq_iff_priorityHolds observed term
    (canonicalReturnChannel observed term)).1 rfl

/-- Membership in the positive-inner matched base is invariant. -/
@[simp] theorem mem_positiveInnerMatchedIteratedQuadraticTerms_flip_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    flipMatchedIteratedQuadraticInnerBranch observed term ∈
        positiveInnerMatchedIteratedQuadraticTerms m observed ↔
      term ∈ positiveInnerMatchedIteratedQuadraticTerms m observed := by
  classical
  unfold positiveInnerMatchedIteratedQuadraticTerms
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    flipMatchedIteratedQuadraticInnerBranch_coe,
    positiveInner_flipIteratedQuadraticInnerBranch_iff]

/-- Each disjoint canonical priority fiber is invariant under the flip. -/
@[simp] theorem mem_positiveInnerCanonicalReturnChannelTerms_flip_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (channel : CanonicalReturnChannel)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    flipMatchedIteratedQuadraticInnerBranch observed term ∈
        positiveInnerCanonicalReturnChannelTerms m observed channel ↔
      term ∈ positiveInnerCanonicalReturnChannelTerms
        m observed channel := by
  classical
  unfold positiveInnerCanonicalReturnChannelTerms
    canonicalReturnChannelFiber
  simp only [Finset.mem_filter,
    mem_positiveInnerMatchedIteratedQuadraticTerms_flip_iff,
    canonicalReturnChannel_flipMatchedIteratedQuadraticInnerBranch]

/-- The compact static weight is odd under the flip.  Every tensor, radius,
carrier, and denominator factor is fixed; only the explicit coordinate
branch sign changes. -/
@[simp] theorem compactIteratedQuadraticStaticFeedbackWeight_flip
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa radius observed
        (flipIteratedQuadraticInnerBranch term) =
      -compactIteratedQuadraticStaticFeedbackWeight
        m kappa radius observed term := by
  unfold compactIteratedQuadraticStaticFeedbackWeight
  simp only [flipIteratedQuadraticInnerBranch_innerEntry,
    firstPicardCoordinateBranchSign_other,
    flipIteratedQuadraticInnerBranch_outerModes,
    flipIteratedQuadraticInnerBranch_firstPicardMode,
    flipIteratedQuadraticInnerBranch_freeMode,
    flipQuadraticPhaseTermRawSigns]
  ring

/-- The branch component prevents a fixed point, independently of the two
raw signs. -/
theorem flipIteratedQuadraticInnerBranch_ne
    {N : Nat} (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    flipIteratedQuadraticInnerBranch term ≠ term := by
  intro heq
  have hbranch := congrArg
    (fun candidate : IteratedQuadraticSecondPicardCharacterTerm N ↦
      (iteratedQuadraticInnerEntry candidate).2) heq
  simp only [flipIteratedQuadraticInnerBranch_innerEntry] at hbranch
  exact otherQuadraticSlot_ne_self
    (iteratedQuadraticInnerEntry term).2 hbranch

/-- Two same-mode signed legs have cancelling charges whenever their phase
signs differ. -/
theorem add_signedMode_charge_eq_zero_of_mode_eq_sign_ne
    {d : Type*} [DecidableEq d] (left right : SignedMode d)
    (hmodes : left.mode = right.mode)
    (hsigns : left.sign ≠ right.sign) :
    left.charge + right.charge = 0 := by
  rcases left with ⟨leftMode, leftSign⟩
  rcases right with ⟨rightMode, rightSign⟩
  dsimp only at hmodes hsigns ⊢
  subst rightMode
  exact (add_signedMode_charge_eq_zero_of_same_mode_iff
    leftMode leftSign rightSign).2 hsigns

/-- On either tadpole channel the adjusted inner pair has zero total charge.
This is the essential extra hypothesis behind mismatch evenness. -/
theorem physlibFirstPicardCoordinateCharge_eq_zero_of_tadpole
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (htadpole : MatchedIteratedQuadraticTadpoleChannel observed term) :
    physlibQuadraticFirstPicardCoordinateCharacterCharge
        (iteratedQuadraticInnerEntry term) = 0 := by
  rw [physlibFirstPicardCoordinateCharge_eq_adjustedInnerLegs]
  rcases htadpole with hzeroOne | honeZero
  · unfold FreeObservedInnerZeroCancelsInnerOne at hzeroOne
    dsimp only at hzeroOne
    rcases hzeroOne with
      ⟨_hfree, hzero, hone, _hobserved, hmodes⟩
    apply add_signedMode_charge_eq_zero_of_mode_eq_sign_ne _ _ hmodes
    intro heq
    have := congrArg id heq
    rw [hzero, hone] at this
    contradiction
  · unfold FreeObservedInnerOneCancelsInnerZero at honeZero
    dsimp only at honeZero
    rcases honeZero with
      ⟨_hfree, hzero, hone, _hobserved, hmodes⟩
    apply add_signedMode_charge_eq_zero_of_mode_eq_sign_ne _ _ hmodes.symm
    intro heq
    have := congrArg id heq
    rw [hzero, hone] at this
    contradiction

/-- A zero coordinate-branch charge forces the underlying raw quadratic
charge to vanish on either branch. -/
theorem quadraticPhaseCharge_eq_zero_of_coordinateCharge_eq_zero
    {N : Nat} [NeZero N]
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N)
    (hzero : physlibQuadraticFirstPicardCoordinateCharacterCharge entry = 0) :
    quadraticPhaseCharge entry.1 = 0 := by
  rcases entry with ⟨term, branch⟩
  fin_cases branch
  · simpa using hzero
  · simpa using hzero

/-- On a tadpole tree the flipped mismatch is exactly the negative of the
original mismatch.  This statement is deliberately not asserted for a
general tree. -/
theorem iteratedQuadraticInnerMismatch_flip_eq_neg_of_tadpole
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (htadpole : MatchedIteratedQuadraticTadpoleChannel observed term) :
    iteratedQuadraticInnerMismatch m
        (flipIteratedQuadraticInnerBranch term) =
      -iteratedQuadraticInnerMismatch m term := by
  have hcoordinate :
      physlibQuadraticFirstPicardCoordinateCharacterCharge
          (iteratedQuadraticInnerEntry term) = 0 :=
    physlibFirstPicardCoordinateCharge_eq_zero_of_tadpole
      observed term htadpole
  have hraw : quadraticPhaseCharge
      (iteratedQuadraticInnerEntry term).1 = 0 :=
    quadraticPhaseCharge_eq_zero_of_coordinateCharge_eq_zero
      (iteratedQuadraticInnerEntry term) hcoordinate
  have hcoordinateFlip :
      physlibQuadraticFirstPicardCoordinateCharacterCharge
          (iteratedQuadraticInnerEntry
            (flipIteratedQuadraticInnerBranch term)) = 0 := by
    rw [physlibFirstPicardCoordinateCharge_flipIteratedQuadraticInnerBranch,
      hcoordinate]
  have hrawFlip : quadraticPhaseCharge
      (iteratedQuadraticInnerEntry
        (flipIteratedQuadraticInnerBranch term)).1 = 0 :=
    quadraticPhaseCharge_eq_zero_of_coordinateCharge_eq_zero
      (iteratedQuadraticInnerEntry
        (flipIteratedQuadraticInnerBranch term)) hcoordinateFlip
  unfold iteratedQuadraticInnerMismatch
    firstPicardCoordinateBranchMismatch
  rw [quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
    quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
    hraw, hrawFlip]
  simp only [chargeFrequency, Pi.zero_apply, Int.cast_zero, zero_mul,
    Finset.sum_const_zero, sub_zero,
    flipIteratedQuadraticInnerBranch_firstPicardMode,
    flipIteratedQuadraticInnerBranch_innerEntry,
    firstPicardCoordinateBranchSign_other]
  ring

/-- Evenness of the finite-time profile turns the preceding mismatch sign
flip into equality of resonance weights. -/
theorem finiteTimeResonanceWeight_innerMismatch_flip_eq_of_tadpole
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (htadpole : MatchedIteratedQuadraticTadpoleChannel observed term) :
    finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m
          (flipIteratedQuadraticInnerBranch term)) time =
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term) time := by
  rw [iteratedQuadraticInnerMismatch_flip_eq_neg_of_tadpole
    m observed term htadpole, finiteTimeResonanceWeight_neg]

/-- The full compact finite-time summand is antisymmetric on a tadpole
tree. -/
theorem compactFeedbackSummand_flip_eq_neg_of_tadpole
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (htadpole : MatchedIteratedQuadraticTadpoleChannel observed term) :
    compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed
          (flipIteratedQuadraticInnerBranch term) *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m
            (flipIteratedQuadraticInnerBranch term)) time =
      -(compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed term *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term) time) := by
  rw [compactIteratedQuadraticStaticFeedbackWeight_flip,
    finiteTimeResonanceWeight_innerMismatch_flip_eq_of_tadpole
      m observed time term htadpole]
  ring

/-- The matched subtype involution has no fixed point because its raw tree
has no fixed point. -/
theorem flipMatchedIteratedQuadraticInnerBranch_ne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    flipMatchedIteratedQuadraticInnerBranch observed term ≠ term := by
  intro heq
  apply flipIteratedQuadraticInnerBranch_ne term.1
  exact congrArg Subtype.val heq

/-- Soundness of a canonical priority fiber, stated in the form needed by
the two tadpole cancellation proofs. -/
theorem rawHolds_of_mem_positiveInnerCanonicalReturnChannelTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (channel : CanonicalReturnChannel)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hterm : term ∈ positiveInnerCanonicalReturnChannelTerms
      m observed channel) :
    channel.RawHolds observed term.1 := by
  have hlabel : canonicalReturnChannel observed term = channel := by
    exact (Finset.mem_filter.mp hterm).2
  have hraw := canonicalReturnChannel_rawHolds observed term
  rwa [hlabel] at hraw

/-- Every member of priority fiber one is a physical tadpole tree. -/
theorem tadpole_of_mem_positiveInnerCanonicalChannelOne
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hterm : term ∈ positiveInnerCanonicalReturnChannelTerms m observed
      .freeObservedInnerZeroCancelsInnerOne) :
    MatchedIteratedQuadraticTadpoleChannel observed term.1 := by
  left
  simpa only [CanonicalReturnChannel.RawHolds] using
    rawHolds_of_mem_positiveInnerCanonicalReturnChannelTerms
      m observed .freeObservedInnerZeroCancelsInnerOne term hterm

/-- Every member of priority fiber three is a physical tadpole tree. -/
theorem tadpole_of_mem_positiveInnerCanonicalChannelThree
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hterm : term ∈ positiveInnerCanonicalReturnChannelTerms m observed
      .freeObservedInnerOneCancelsInnerZero) :
    MatchedIteratedQuadraticTadpoleChannel observed term.1 := by
  right
  simpa only [CanonicalReturnChannel.RawHolds] using
    rawHolds_of_mem_positiveInnerCanonicalReturnChannelTerms
      m observed .freeObservedInnerOneCancelsInnerZero term hterm

/-- Exact cancellation of the first canonical tadpole priority fiber. -/
theorem canonicalTadpoleChannelOne_compactFeedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerCanonicalReturnChannelTerms m observed
        .freeObservedInnerZeroCancelsInnerOne,
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) = 0 := by
  classical
  apply Finset.sum_involution
    (fun term _hterm ↦
      flipMatchedIteratedQuadraticInnerBranch observed term)
  · intro term hterm
    change
      compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time +
        compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed
            (flipIteratedQuadraticInnerBranch term.1) *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m
              (flipIteratedQuadraticInnerBranch term.1)) time = 0
    rw [compactFeedbackSummand_flip_eq_neg_of_tadpole
      m kappa time radius observed term.1
      (tadpole_of_mem_positiveInnerCanonicalChannelOne
        m observed term hterm)]
    ring
  · intro term _hterm _hnonzero
    exact flipMatchedIteratedQuadraticInnerBranch_ne observed term
  · intro term hterm
    exact (mem_positiveInnerCanonicalReturnChannelTerms_flip_iff
      m observed .freeObservedInnerZeroCancelsInnerOne term).2 hterm
  · intro term _hterm
    exact flipMatchedIteratedQuadraticInnerBranch_involutive observed term

/-- Exact cancellation of the third canonical tadpole priority fiber. -/
theorem canonicalTadpoleChannelThree_compactFeedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerCanonicalReturnChannelTerms m observed
        .freeObservedInnerOneCancelsInnerZero,
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) = 0 := by
  classical
  apply Finset.sum_involution
    (fun term _hterm ↦
      flipMatchedIteratedQuadraticInnerBranch observed term)
  · intro term hterm
    change
      compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time +
        compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed
            (flipIteratedQuadraticInnerBranch term.1) *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m
              (flipIteratedQuadraticInnerBranch term.1)) time = 0
    rw [compactFeedbackSummand_flip_eq_neg_of_tadpole
      m kappa time radius observed term.1
      (tadpole_of_mem_positiveInnerCanonicalChannelThree
        m observed term hterm)]
    ring
  · intro term _hterm _hnonzero
    exact flipMatchedIteratedQuadraticInnerBranch_ne observed term
  · intro term hterm
    exact (mem_positiveInnerCanonicalReturnChannelTerms_flip_iff
      m observed .freeObservedInnerOneCancelsInnerZero term).2 hterm
  · intro term _hterm
    exact flipMatchedIteratedQuadraticInnerBranch_involutive observed term

/-- The sum of the two disjoint canonical tadpole fibers vanishes.  Since
these are selector fibers, an all-equal raw overlap belongs to only its
first-priority channel and is never counted twice. -/
theorem canonicalTadpoleFibers_compactFeedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerCanonicalReturnChannelTerms m observed
        .freeObservedInnerZeroCancelsInnerOne,
      compactIteratedQuadraticStaticFeedbackWeight
          m kappa radius observed term.1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m term.1) time) +
      (∑ term ∈ positiveInnerCanonicalReturnChannelTerms m observed
          .freeObservedInnerOneCancelsInnerZero,
        compactIteratedQuadraticStaticFeedbackWeight
            m kappa radius observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time) = 0 := by
  rw [canonicalTadpoleChannelOne_compactFeedbackSum_eq_zero,
    canonicalTadpoleChannelThree_compactFeedbackSum_eq_zero]
  norm_num

end


end ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
