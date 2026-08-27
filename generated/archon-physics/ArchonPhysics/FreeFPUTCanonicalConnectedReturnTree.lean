import ArchonPhysics.FreeFPUTConnectedReturnCollisionKernelBridge
import ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry

/-!
# Canonical local constructors for connected quadratic return trees

For one ordered quadratic phase term `q` and one distinguished input `r`,
this module constructs the four literal connected return trees obtained from
the two outer placements and the two inner placements.  The construction is
local in `q`: no injectivity across distinct raw quadratic terms is claimed.
Indeed, simultaneously swapping `q` and replacing `r` by its opposite gives
the same oriented data, so a later global reindex must use swap-orbit
representatives or retain the corresponding multiplicity.
-/

namespace ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTConnectedReturnCollisionKernelBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ResonanceWeightSinc
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- The observed mode and the two modes of a quadratic term are pairwise
distinct, in the exact elementary form needed by the local injectivity
proof. -/
def ObservedQuadraticAllDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Prop :=
  q.1 0 ≠ q.1 1 ∧ observed ≠ q.1 0 ∧ observed ≠ q.1 1

/-- Put one value in a selected binary slot and another value in its
opposite slot. -/
def twoSlotPlacement {α : Type*} (selected : Fin 2)
    (selectedValue otherValue : α) : Fin 2 → α :=
  fun slot ↦ if slot = selected then selectedValue else otherValue

@[simp] theorem twoSlotPlacement_selected {α : Type*} (selected : Fin 2)
    (selectedValue otherValue : α) :
    twoSlotPlacement selected selectedValue otherValue selected =
      selectedValue := by
  simp [twoSlotPlacement]

@[simp] theorem twoSlotPlacement_other {α : Type*} (selected : Fin 2)
    (selectedValue otherValue : α) :
    twoSlotPlacement selected selectedValue otherValue
        (otherQuadraticSlot selected) = otherValue := by
  fin_cases selected <;> simp [twoSlotPlacement]

@[simp] theorem otherQuadraticSlot_involutive (slot : Fin 2) :
    otherQuadraticSlot (otherQuadraticSlot slot) = slot := by
  fin_cases slot <;> simp

theorem otherQuadraticSlot_ne_self (slot : Fin 2) :
    otherQuadraticSlot slot ≠ slot := by
  fin_cases slot <;> simp

/-- Applying the coordinate-branch sign adjustment twice restores the raw
binary phase sign. -/
@[simp] theorem coordinateBranchAdjustedBinarySign_involutive
    (branch sign : Fin 2) :
    coordinateBranchAdjustedBinarySign branch
        (coordinateBranchAdjustedBinarySign branch sign) = sign := by
  fin_cases branch <;> fin_cases sign <;>
    simp [coordinateBranchAdjustedBinarySign]

/-- Outer modes, with the distinguished input at the selected `Q1` slot. -/
def connectedReturnOuterModes
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (r outerSlot : Fin 2) : Fin 2 → Lattice.Site N :=
  twoSlotPlacement outerSlot (q.1 r)
    (q.1 (otherQuadraticSlot r))

/-- Inner modes after the coordinate-branch adjustment: the selected input
is the observed positive leg and the other input cancels the free leg. -/
def connectedReturnInnerModes
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r innerSlot : Fin 2) :
    Fin 2 → Lattice.Site N :=
  twoSlotPlacement innerSlot observed
    (q.1 (otherQuadraticSlot r))

/-- Desired binary signs after applying the real-coordinate branch. -/
def connectedReturnAdjustedInnerSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (r innerSlot : Fin 2) : Fin 2 → Fin 2 :=
  twoSlotPlacement innerSlot 0
    (otherQuadraticSlot
      (quadraticPhaseTermBinarySign q (otherQuadraticSlot r)))

/-- Raw inner signs.  Applying the same branch adjustment again recovers the
desired adjusted signs because that adjustment is an involution. -/
def connectedReturnRawInnerSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (r innerSlot input : Fin 2) : Fin 2 :=
  coordinateBranchAdjustedBinarySign
    (quadraticPhaseTermBinarySign q r)
    (connectedReturnAdjustedInnerSign q r innerSlot input)

/-- Raw inner quadratic term of one connected return tree. -/
def connectedReturnInnerTerm
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r innerSlot : Fin 2) :
    QuadraticPhaseTerm N :=
  (connectedReturnInnerModes observed q r innerSlot,
    (connectedReturnRawInnerSign q r innerSlot 0,
      connectedReturnRawInnerSign q r innerSlot 1))

/-- One literal connected return tree.  Varying `outerSlot` and `innerSlot`
gives the four local placements associated with fixed `q` and `r`. -/
def connectedReturnTree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    IteratedQuadraticSecondPicardCharacterTerm N :=
  (connectedReturnOuterModes q r outerSlot,
    outerSlot,
    quadraticPhaseTermBinarySign q (otherQuadraticSlot r),
    connectedReturnInnerTerm observed q r innerSlot,
    quadraticPhaseTermBinarySign q r)

@[simp] theorem connectedReturnTree_outerModes
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticOuterModes
        (connectedReturnTree observed q r outerSlot innerSlot) =
      connectedReturnOuterModes q r outerSlot := rfl

@[simp] theorem connectedReturnTree_firstPicardSlot
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticFirstPicardSlot
        (connectedReturnTree observed q r outerSlot innerSlot) =
      outerSlot := rfl

@[simp] theorem connectedReturnTree_freeSign
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticFreeSign
        (connectedReturnTree observed q r outerSlot innerSlot) =
      quadraticPhaseTermBinarySign q (otherQuadraticSlot r) := rfl

@[simp] theorem connectedReturnTree_innerEntry
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticInnerEntry
        (connectedReturnTree observed q r outerSlot innerSlot) =
      (connectedReturnInnerTerm observed q r innerSlot,
        quadraticPhaseTermBinarySign q r) := rfl

@[simp] theorem connectedReturnTree_firstPicardMode
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticFirstPicardMode
        (connectedReturnTree observed q r outerSlot innerSlot) = q.1 r := by
  simp [iteratedQuadraticFirstPicardMode, connectedReturnOuterModes]

@[simp] theorem connectedReturnTree_freeMode
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticFreeMode
        (connectedReturnTree observed q r outerSlot innerSlot) =
      q.1 (otherQuadraticSlot r) := by
  simp [iteratedQuadraticFreeMode, connectedReturnOuterModes]

@[simp] theorem connectedReturnInnerTerm_modes
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r innerSlot : Fin 2) :
    (connectedReturnInnerTerm observed q r innerSlot).1 =
      connectedReturnInnerModes observed q r innerSlot := rfl

@[simp] theorem quadraticPhaseTermBinarySign_connectedReturnInnerTerm
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r innerSlot input : Fin 2) :
    quadraticPhaseTermBinarySign
        (connectedReturnInnerTerm observed q r innerSlot) input =
      connectedReturnRawInnerSign q r innerSlot input := by
  fin_cases input <;> rfl

@[simp] theorem connectedReturnTree_freeSignedLeg
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticFreeSignedLeg
        (connectedReturnTree observed q r outerSlot innerSlot) =
      binarySignedMode (q.1 (otherQuadraticSlot r))
        (quadraticPhaseTermBinarySign q (otherQuadraticSlot r)) := by
  simp [iteratedQuadraticFreeSignedLeg]

@[simp] theorem adjustedFirstPicardInnerLeg_connectedReturnInnerTerm_selected
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r innerSlot : Fin 2) :
    adjustedFirstPicardInnerLeg
        (connectedReturnInnerTerm observed q r innerSlot,
          quadraticPhaseTermBinarySign q r)
        innerSlot = positiveSignedMode observed := by
  unfold adjustedFirstPicardInnerLeg
  rw [quadraticPhaseTermBinarySign_connectedReturnInnerTerm]
  unfold connectedReturnRawInnerSign
  rw [coordinateBranchAdjustedBinarySign_involutive]
  simp [connectedReturnInnerTerm, connectedReturnInnerModes,
    connectedReturnAdjustedInnerSign, positiveSignedMode,
    binarySignedMode]

@[simp] theorem adjustedFirstPicardInnerLeg_connectedReturnInnerTerm_other
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r innerSlot : Fin 2) :
    adjustedFirstPicardInnerLeg
        (connectedReturnInnerTerm observed q r innerSlot,
          quadraticPhaseTermBinarySign q r)
        (otherQuadraticSlot innerSlot) =
      binarySignedMode (q.1 (otherQuadraticSlot r))
        (otherQuadraticSlot
          (quadraticPhaseTermBinarySign q (otherQuadraticSlot r))) := by
  unfold adjustedFirstPicardInnerLeg
  rw [quadraticPhaseTermBinarySign_connectedReturnInnerTerm]
  unfold connectedReturnRawInnerSign
  rw [coordinateBranchAdjustedBinarySign_involutive]
  simp [connectedReturnInnerTerm, connectedReturnInnerModes,
    connectedReturnAdjustedInnerSign]

@[simp] theorem connectedReturnTree_adjustedInnerLeg_selected
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    adjustedFirstPicardInnerLeg
        (iteratedQuadraticInnerEntry
          (connectedReturnTree observed q r outerSlot innerSlot))
        innerSlot = positiveSignedMode observed := by
  exact adjustedFirstPicardInnerLeg_connectedReturnInnerTerm_selected
    observed q r innerSlot

@[simp] theorem connectedReturnTree_adjustedInnerLeg_other
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    adjustedFirstPicardInnerLeg
        (iteratedQuadraticInnerEntry
          (connectedReturnTree observed q r outerSlot innerSlot))
        (otherQuadraticSlot innerSlot) =
      binarySignedMode (q.1 (otherQuadraticSlot r))
        (otherQuadraticSlot
          (quadraticPhaseTermBinarySign q (otherQuadraticSlot r))) := by
  exact adjustedFirstPicardInnerLeg_connectedReturnInnerTerm_other
    observed q r innerSlot

/-- Opposite binary characters at one mode have cancelling charges. -/
theorem binarySignedMode_charge_add_otherQuadraticSlot
    {N : Nat} [NeZero N] (mode : Lattice.Site N) (sign : Fin 2) :
    (binarySignedMode mode sign).charge +
        (binarySignedMode mode (otherQuadraticSlot sign)).charge = 0 := by
  fin_cases sign <;>
    simp [binarySignedMode, binaryPhaseSign, SignedMode.charge,
      PhaseSign.exponent, Pi.single_neg]

/-- The constructor is charge matched without any distinct-mode hypothesis. -/
theorem connectedReturnTree_chargeMatched
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge
        (Sum.inl (connectedReturnTree observed q r outerSlot innerSlot)) := by
  rw [completeSecondPicardCharge_inl,
    iteratedQuadraticSecondPicardCharge_eq_threeLegs]
  rw [connectedReturnTree_freeSignedLeg]
  have hinnerSum :
      (adjustedFirstPicardInnerLeg
          (iteratedQuadraticInnerEntry
            (connectedReturnTree observed q r outerSlot innerSlot)) 0).charge +
        (adjustedFirstPicardInnerLeg
          (iteratedQuadraticInnerEntry
            (connectedReturnTree observed q r outerSlot innerSlot)) 1).charge =
      (adjustedFirstPicardInnerLeg
          (iteratedQuadraticInnerEntry
            (connectedReturnTree observed q r outerSlot innerSlot))
          innerSlot).charge +
        (adjustedFirstPicardInnerLeg
          (iteratedQuadraticInnerEntry
            (connectedReturnTree observed q r outerSlot innerSlot))
          (otherQuadraticSlot innerSlot)).charge := by
    fin_cases innerSlot
    · rfl
    · exact add_comm _ _
  rw [show
      (binarySignedMode (q.1 (otherQuadraticSlot r))
            (quadraticPhaseTermBinarySign q (otherQuadraticSlot r))).charge +
          (adjustedFirstPicardInnerLeg
            (iteratedQuadraticInnerEntry
              (connectedReturnTree observed q r outerSlot innerSlot)) 0).charge +
          (adjustedFirstPicardInnerLeg
            (iteratedQuadraticInnerEntry
              (connectedReturnTree observed q r outerSlot innerSlot)) 1).charge =
        (binarySignedMode (q.1 (otherQuadraticSlot r))
            (quadraticPhaseTermBinarySign q (otherQuadraticSlot r))).charge +
          ((adjustedFirstPicardInnerLeg
            (iteratedQuadraticInnerEntry
              (connectedReturnTree observed q r outerSlot innerSlot)) 0).charge +
          (adjustedFirstPicardInnerLeg
            (iteratedQuadraticInnerEntry
              (connectedReturnTree observed q r outerSlot innerSlot)) 1).charge) by
        abel,
    hinnerSum,
    connectedReturnTree_adjustedInnerLeg_selected,
    connectedReturnTree_adjustedInnerLeg_other]
  have hcancel := binarySignedMode_charge_add_otherQuadraticSlot
    (q.1 (otherQuadraticSlot r))
    (quadraticPhaseTermBinarySign q (otherQuadraticSlot r))
  simp only [freeInitialPhaseCharge]
  change (positiveSignedMode observed).charge = _
  rw [show
      (binarySignedMode (q.1 (otherQuadraticSlot r))
            (quadraticPhaseTermBinarySign q (otherQuadraticSlot r))).charge +
          ((positiveSignedMode observed).charge +
            (binarySignedMode (q.1 (otherQuadraticSlot r))
              (otherQuadraticSlot
                (quadraticPhaseTermBinarySign q
                  (otherQuadraticSlot r)))).charge) =
        (positiveSignedMode observed).charge +
          ((binarySignedMode (q.1 (otherQuadraticSlot r))
            (quadraticPhaseTermBinarySign q (otherQuadraticSlot r))).charge +
          (binarySignedMode (q.1 (otherQuadraticSlot r))
            (otherQuadraticSlot
              (quadraticPhaseTermBinarySign q
                (otherQuadraticSlot r)))).charge) by abel,
    hcancel, add_zero]

/-- The charge witness packaged in the exact matched subtype. -/
def matchedConnectedReturnTree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    FreeInitialMatchedIteratedQuadraticTerm N observed :=
  ⟨connectedReturnTree observed q r outerSlot innerSlot,
    connectedReturnTree_chargeMatched observed q r outerSlot innerSlot⟩

/-- Every constructed tree is in one of the four connected return channels;
no distinctness is needed. -/
theorem connectedReturnTree_connectedChannel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    MatchedIteratedQuadraticConnectedChannel observed
      (connectedReturnTree observed q r outerSlot innerSlot) := by
  unfold MatchedIteratedQuadraticConnectedChannel
  by_cases hinner : innerSlot = 0
  · subst innerSlot
    have hotherZero :=
      connectedReturnTree_adjustedInnerLeg_other observed q r outerSlot (0 : Fin 2)
    simp only [otherQuadraticSlot_zero] at hotherZero
    by_cases hfree :
        quadraticPhaseTermBinarySign q (otherQuadraticSlot r) = 0
    · left
      unfold InnerZeroObservedFreeCancelsInnerOne
      rw [connectedReturnTree_freeSignedLeg,
        connectedReturnTree_adjustedInnerLeg_selected,
        hotherZero]
      simp [hfree, binarySignedMode, binaryPhaseSign]
    · have hfreeOne :
          quadraticPhaseTermBinarySign q (otherQuadraticSlot r) = 1 :=
        Fin.eq_one_of_ne_zero _ hfree
      right
      right
      left
      unfold InnerZeroObservedInnerOneCancelsFree
      rw [connectedReturnTree_freeSignedLeg,
        connectedReturnTree_adjustedInnerLeg_selected,
        hotherZero]
      simp [hfreeOne, binarySignedMode, binaryPhaseSign]
  · have hinnerOne : innerSlot = 1 :=
      Fin.eq_one_of_ne_zero _ hinner
    subst innerSlot
    have hotherOne :=
      connectedReturnTree_adjustedInnerLeg_other observed q r outerSlot (1 : Fin 2)
    simp only [otherQuadraticSlot_one] at hotherOne
    by_cases hfree :
        quadraticPhaseTermBinarySign q (otherQuadraticSlot r) = 0
    · right
      left
      unfold InnerOneObservedFreeCancelsInnerZero
      rw [connectedReturnTree_freeSignedLeg,
        connectedReturnTree_adjustedInnerLeg_selected,
        hotherOne]
      simp [hfree, binarySignedMode, binaryPhaseSign]
    · have hfreeOne :
          quadraticPhaseTermBinarySign q (otherQuadraticSlot r) = 1 :=
        Fin.eq_one_of_ne_zero _ hfree
      right
      right
      right
      unfold InnerOneObservedInnerZeroCancelsFree
      rw [connectedReturnTree_freeSignedLeg,
        connectedReturnTree_adjustedInnerLeg_selected,
        hotherOne]
      simp [hfreeOne, binarySignedMode, binaryPhaseSign]

/-- The two inner children are exactly the observed and free modes, so the
generic connected-pairing bridge applies. -/
theorem connectedReturnTree_connectedPairing
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    ConnectedReturnModePairing observed
      (connectedReturnTree observed q r outerSlot innerSlot) := by
  unfold ConnectedReturnModePairing
  fin_cases innerSlot
  · left
    simp [connectedReturnInnerTerm, connectedReturnInnerModes,
      twoSlotPlacement]
  · right
    simp [connectedReturnInnerTerm, connectedReturnInnerModes,
      twoSlotPlacement]

/-- Permutation taking the original collision tuple to the raw inner tuple.
When the inner observed slot differs from `r`, the two input positions are
also exchanged after swapping the output with input `r`. -/
def connectedReturnCollisionPermutation
    (r innerSlot : Fin 2) : Equiv.Perm (Fin 3) :=
  if innerSlot = r then
    Equiv.swap 0 (Fin.succ r)
  else
    quadraticCollisionLegSwap.trans (Equiv.swap 0 (Fin.succ r))

@[simp] theorem connectedReturnCollisionPermutation_zero
    (r innerSlot : Fin 2) :
    connectedReturnCollisionPermutation r innerSlot 0 = Fin.succ r := by
  fin_cases r <;> fin_cases innerSlot <;> decide

@[simp] theorem connectedReturnCollisionPermutation_innerSlot
    (r innerSlot : Fin 2) :
    connectedReturnCollisionPermutation r innerSlot (Fin.succ innerSlot) =
      0 := by
  fin_cases r <;> fin_cases innerSlot <;> decide

@[simp] theorem connectedReturnCollisionPermutation_otherInnerSlot
    (r innerSlot : Fin 2) :
    connectedReturnCollisionPermutation r innerSlot
        (Fin.succ (otherQuadraticSlot innerSlot)) =
      Fin.succ (otherQuadraticSlot r) := by
  fin_cases r <;> fin_cases innerSlot <;> decide

@[simp] theorem connectedReturnCollisionPermutation_zero_one (r : Fin 2) :
    connectedReturnCollisionPermutation r 0 1 = 0 := by
  fin_cases r <;> decide

@[simp] theorem connectedReturnCollisionPermutation_zero_two (r : Fin 2) :
    connectedReturnCollisionPermutation r 0 2 =
      Fin.succ (otherQuadraticSlot r) := by
  fin_cases r <;> decide

@[simp] theorem connectedReturnCollisionPermutation_one_one (r : Fin 2) :
    connectedReturnCollisionPermutation r 1 1 =
      Fin.succ (otherQuadraticSlot r) := by
  fin_cases r <;> decide

@[simp] theorem connectedReturnCollisionPermutation_one_two (r : Fin 2) :
    connectedReturnCollisionPermutation r 1 2 = 0 := by
  fin_cases r <;> decide

@[simp] theorem quadraticCollisionModes_one
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    quadraticCollisionModes observed q 1 = q.1 0 := rfl

@[simp] theorem quadraticCollisionModes_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    quadraticCollisionModes observed q 0 = observed := rfl

@[simp] theorem quadraticCollisionModes_succ
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2) :
    quadraticCollisionModes observed q (Fin.succ r) = q.1 r := rfl

@[simp] theorem quadraticCollisionModes_two
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    quadraticCollisionModes observed q 2 = q.1 1 := rfl

@[simp] theorem quadraticCollisionSign_one
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) :
    quadraticCollisionSign q 1 =
      phaseSignToInputInteractionSign (binaryPhaseSign q.2.1) := rfl

@[simp] theorem quadraticCollisionSign_zero
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) :
    quadraticCollisionSign q 0 = .plus := rfl

@[simp] theorem quadraticCollisionSign_succ
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) (r : Fin 2) :
    quadraticCollisionSign q (Fin.succ r) =
      quadraticInputInteractionSign q r := rfl

@[simp] theorem quadraticCollisionSign_two
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) :
    quadraticCollisionSign q 2 =
      phaseSignToInputInteractionSign (binaryPhaseSign q.2.2) := rfl

/-- The raw inner collision modes are a permutation of the original three
modes. -/
theorem quadraticCollisionModes_connectedReturnInnerTerm
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r innerSlot : Fin 2) :
    quadraticCollisionModes (q.1 r)
        (connectedReturnInnerTerm observed q r innerSlot) =
      quadraticCollisionModes observed q ∘
        connectedReturnCollisionPermutation r innerSlot := by
  funext leg
  fin_cases innerSlot <;> fin_cases leg <;>
    simp [connectedReturnInnerTerm, connectedReturnInnerModes,
      twoSlotPlacement, Function.comp_apply]

/-- On branch zero the raw inner sign tuple is the globally reversed
permutation of the original tuple; on branch one it is just the permutation.
-/
theorem quadraticCollisionSign_connectedReturnInnerTerm
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r innerSlot : Fin 2) :
    quadraticCollisionSign
        (connectedReturnInnerTerm observed q r innerSlot) =
      if quadraticPhaseTermBinarySign q r = 0 then
        reverseSignPattern
          (quadraticCollisionSign q ∘
            connectedReturnCollisionPermutation r innerSlot)
      else
        quadraticCollisionSign q ∘
          connectedReturnCollisionPermutation r innerSlot := by
  rcases q with ⟨modes, signZero, signOne⟩
  funext leg
  fin_cases signZero <;> fin_cases signOne <;>
    fin_cases r <;> fin_cases innerSlot <;> fin_cases leg <;>
    simp [connectedReturnInnerTerm, connectedReturnRawInnerSign,
      connectedReturnAdjustedInnerSign, reverseSignPattern, oppositeSign,
      phaseSignToInputInteractionSign, coordinateBranchAdjustedBinarySign,
      quadraticPhaseTermBinarySign, twoSlotPlacement, Function.comp_apply]

/-- The raw inner finite-time kernel equals the original `q` kernel by
permutation invariance, with global sign reversal on branch zero. -/
theorem finiteTimeCollisionKernel_connectedReturnInnerTerm_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (r innerSlot : Fin 2) :
    finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign
          (connectedReturnInnerTerm observed q r innerSlot)) time
        (quadraticCollisionModes (q.1 r)
          (connectedReturnInnerTerm observed q r innerSlot)) =
      finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q) := by
  rw [quadraticCollisionSign_connectedReturnInnerTerm,
    quadraticCollisionModes_connectedReturnInnerTerm]
  by_cases hbranch : quadraticPhaseTermBinarySign q r = 0
  · rw [if_pos hbranch,
      finiteTimeCollisionKernel_reverseSignPattern,
      finiteTimeCollisionKernel_perm]
  · rw [if_neg hbranch, finiteTimeCollisionKernel_perm]

/-- Before the coordinate-branch multiplier, the raw inner mismatch is the
negative branch sign times the original mismatch. -/
theorem quadraticPhaseMismatch_connectedReturnInnerTerm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (r innerSlot : Fin 2) :
    quadraticPhaseMismatch (modeFrequency m) (q.1 r)
        (connectedReturnInnerTerm observed q r innerSlot) =
      -firstPicardCoordinateBranchSign
          (quadraticPhaseTermBinarySign q r) *
        quadraticPhaseMismatch (modeFrequency m) observed q := by
  rw [quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch,
    quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch,
    quadraticCollisionSign_connectedReturnInnerTerm,
    quadraticCollisionModes_connectedReturnInnerTerm]
  by_cases hbranch : quadraticPhaseTermBinarySign q r = 0
  · rw [if_pos hbranch, phaseMismatch_reverseSignPattern,
      phaseMismatch_perm]
    simp [hbranch, firstPicardCoordinateBranchSign]
  · have hbranchOne : quadraticPhaseTermBinarySign q r = 1 :=
      Fin.eq_one_of_ne_zero _ hbranch
    rw [if_neg hbranch, phaseMismatch_perm]
    simp [hbranchOne, firstPicardCoordinateBranchSign]

/-- After the real-coordinate branch multiplier, every constructed inner
mismatch is exactly the negative of the original `q` mismatch. -/
theorem connectedReturnTree_innerMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (r outerSlot innerSlot : Fin 2) :
    iteratedQuadraticInnerMismatch m
        (connectedReturnTree observed q r outerSlot innerSlot) =
      -quadraticPhaseMismatch (modeFrequency m) observed q := by
  unfold iteratedQuadraticInnerMismatch
    firstPicardCoordinateBranchMismatch
  rw [connectedReturnTree_firstPicardMode,
    connectedReturnTree_innerEntry,
    quadraticPhaseMismatch_connectedReturnInnerTerm]
  rw [show
    firstPicardCoordinateBranchSign
          (quadraticPhaseTermBinarySign q r) *
        (-firstPicardCoordinateBranchSign
            (quadraticPhaseTermBinarySign q r) *
          quadraticPhaseMismatch (modeFrequency m) observed q) =
      -(firstPicardCoordinateBranchSign
          (quadraticPhaseTermBinarySign q r) ^ 2) *
        quadraticPhaseMismatch (modeFrequency m) observed q by ring,
    firstPicardCoordinateBranchSign_sq]
  ring

@[simp] theorem quadraticInputInteractionSign_apply
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) (r : Fin 2) :
    quadraticInputInteractionSign q r =
      phaseSignToInputInteractionSign
        (binaryPhaseSign (quadraticPhaseTermBinarySign q r)) := by
  fin_cases r <;> rfl

/-- The sign supplied by the return branch is exactly the interaction-sign
coefficient of the distinguished input of `q`. -/
theorem connectedReturnTree_feedbackSign
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2) :
    -firstPicardCoordinateBranchSign
        (iteratedQuadraticInnerEntry
          (connectedReturnTree observed q r outerSlot innerSlot)).2 =
      (quadraticCollisionSign q (Fin.succ r)).coefficient := by
  rw [connectedReturnTree_innerEntry]
  simp only [quadraticCollisionSign, Fin.cons_succ,
    quadraticInputInteractionSign_apply]
  generalize hsign : quadraticPhaseTermBinarySign q r = sign
  fin_cases sign <;>
    simp [phaseSignToInputInteractionSign,
      firstPicardCoordinateBranchSign, binaryPhaseSign]

/-- Positivity of the original tuple transports to the raw inner tuple. -/
theorem positiveModeTuple_connectedReturnInnerTerm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (r innerSlot : Fin 2)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    PositiveModeTuple m
      (quadraticCollisionModes (q.1 r)
        (connectedReturnInnerTerm observed q r innerSlot)) := by
  intro leg
  rw [quadraticCollisionModes_connectedReturnInnerTerm]
  exact hPositive (connectedReturnCollisionPermutation r innerSlot leg)

/-- Termwise physical identity: one local return tree is its distinguished
input sign times the original `q` collision kernel and the observed/other
actions.  The finite-time weight is written with the original `q` mismatch,
using the evenness of the resonance profile. -/
theorem connectedReturnTree_feedback_eq_signedKernel_mul_actions
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed
          (connectedReturnTree observed q r outerSlot innerSlot) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed q) time =
      (quadraticCollisionSign q (Fin.succ r)).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (q.1 (otherQuadraticSlot r))) := by
  have hInnerPositive := positiveModeTuple_connectedReturnInnerTerm
    m observed q r innerSlot hPositive
  have hInnerPositiveTree : PositiveModeTuple m
      (quadraticCollisionModes
        (iteratedQuadraticFirstPicardMode
          (connectedReturnTree observed q r outerSlot innerSlot))
        (iteratedQuadraticInnerEntry
          (connectedReturnTree observed q r outerSlot innerSlot)).1) := by
    simpa using hInnerPositive
  have hgeneric :=
    compactWeight_mul_resonance_eq_collisionKernel_mul_actions_of_pairing
      m kappa time energy observed
      (connectedReturnTree observed q r outerSlot innerSlot)
      hEnergy hInnerPositiveTree
      (connectedReturnTree_connectedPairing observed q r outerSlot innerSlot)
  calc
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed
          (connectedReturnTree observed q r outerSlot innerSlot) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed q) time =
      compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed
          (connectedReturnTree observed q r outerSlot innerSlot) *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m
            (connectedReturnTree observed q r outerSlot innerSlot)) time := by
      rw [connectedReturnTree_innerMismatch,
        finiteTimeResonanceWeight_neg]
    _ = -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry
            (connectedReturnTree observed q r outerSlot innerSlot)).2 *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign
              (connectedReturnInnerTerm observed q r innerSlot)) time
            (quadraticCollisionModes (q.1 r)
              (connectedReturnInnerTerm observed q r innerSlot)) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (q.1 (otherQuadraticSlot r))) := by
      simpa using hgeneric
    _ = (quadraticCollisionSign q (Fin.succ r)).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (q.1 (otherQuadraticSlot r))) := by
      rw [connectedReturnTree_feedbackSign,
        finiteTimeCollisionKernel_connectedReturnInnerTerm_eq]

/-- For fixed `q` and `r`, the two outer and two inner placements give four
distinct raw trees.  Only separation of the observed and other mode is
needed. -/
theorem connectedReturnTree_placement_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r : Fin 2)
    (hObservedOther : observed ≠ q.1 (otherQuadraticSlot r)) :
    Function.Injective
      (fun placement : Fin 2 × Fin 2 ↦
        connectedReturnTree observed q r placement.1 placement.2) := by
  rintro ⟨outerLeft, innerLeft⟩ ⟨outerRight, innerRight⟩ htree
  have houter : outerLeft = outerRight := by
    simpa using congrArg iteratedQuadraticFirstPicardSlot htree
  subst outerRight
  have hinner : innerLeft = innerRight := by
    by_contra hne
    have hmodes := congrArg
      (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
        (iteratedQuadraticInnerEntry term).1.1 innerLeft) htree
    change
      twoSlotPlacement innerLeft observed (q.1 (otherQuadraticSlot r))
          innerLeft =
        twoSlotPlacement innerRight observed (q.1 (otherQuadraticSlot r))
          innerLeft at hmodes
    have hbad : observed = q.1 (otherQuadraticSlot r) := by
      simpa [twoSlotPlacement, hne] using hmodes
    exact hObservedOther hbad
  subst innerRight
  rfl

/-- For fixed ordered `q`, the distinguished input and both placements are
jointly injective under observed/all-input distinctness.  This deliberately
does not quantify over `q`. -/
theorem connectedReturnTree_localIndex_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    Function.Injective
      (fun index : Fin 2 × (Fin 2 × Fin 2) ↦
        connectedReturnTree observed q index.1 index.2.1 index.2.2) := by
  rintro ⟨rLeft, outerLeft, innerLeft⟩
    ⟨rRight, outerRight, innerRight⟩ htree
  have hmodes : q.1 rLeft = q.1 rRight := by
    simpa using congrArg iteratedQuadraticFirstPicardMode htree
  have hr : rLeft = rRight := by
    fin_cases rLeft <;> fin_cases rRight
    · rfl
    · exact (hDistinct.1 hmodes).elim
    · exact (hDistinct.1 hmodes.symm).elim
    · rfl
  subst rRight
  have hObservedOther : observed ≠ q.1 (otherQuadraticSlot rLeft) := by
    fin_cases rLeft
    · simpa using hDistinct.2.2
    · simpa using hDistinct.2.1
  have hplacement : (outerLeft, innerLeft) =
      (outerRight, innerRight) :=
    connectedReturnTree_placement_injective observed q rLeft
      hObservedOther htree
  cases hplacement
  rfl

end

end ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
