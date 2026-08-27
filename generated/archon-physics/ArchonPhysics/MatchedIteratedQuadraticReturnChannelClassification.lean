import ArchonPhysics.ThreeSignedChargeCancellationClassification

/-!
# Six return channels of a charge-matched iterated quadratic tree

The abstract three-charge theorem leaves an unordered choice of which
positive leg is the observed copy.  This module expands that choice into six
explicit ordered return channels.  Two channels have the free outer leg as
the observed copy and an opposite-sign inner pair at one mode; these are
called `tadpole` channels.  The remaining four channels have the observed
copy on an inner leg and connect the free leg to the opposite-sign leg.

The alternatives deliberately need not be disjoint when modes coincide.  In
particular, the all-equal case can satisfy both a tadpole and a connected mode
relation, so no quotient or uniqueness assertion is made here.
-/

namespace ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- `free+`, `inner0+`, `inner1-`, with the free leg carrying the observed
copy and the two inner modes cancelling. -/
def FreeObservedInnerZeroCancelsInnerOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  let freeLeg := iteratedQuadraticFreeSignedLeg term
  let inner₀ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 0
  let inner₁ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 1
  freeLeg.sign = .phase ∧ inner₀.sign = .phase ∧
    inner₁.sign = .conjugate ∧ freeLeg.mode = observed ∧
    inner₀.mode = inner₁.mode

/-- `free+`, `inner0+`, `inner1-`, with inner zero carrying the observed
copy and the free mode cancelling inner one. -/
def InnerZeroObservedFreeCancelsInnerOne
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  let freeLeg := iteratedQuadraticFreeSignedLeg term
  let inner₀ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 0
  let inner₁ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 1
  freeLeg.sign = .phase ∧ inner₀.sign = .phase ∧
    inner₁.sign = .conjugate ∧ inner₀.mode = observed ∧
    freeLeg.mode = inner₁.mode

/-- `free+`, `inner0-`, `inner1+`, with the free leg carrying the observed
copy and the two inner modes cancelling. -/
def FreeObservedInnerOneCancelsInnerZero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  let freeLeg := iteratedQuadraticFreeSignedLeg term
  let inner₀ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 0
  let inner₁ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 1
  freeLeg.sign = .phase ∧ inner₀.sign = .conjugate ∧
    inner₁.sign = .phase ∧ freeLeg.mode = observed ∧
    inner₁.mode = inner₀.mode

/-- `free+`, `inner0-`, `inner1+`, with inner one carrying the observed
copy and the free mode cancelling inner zero. -/
def InnerOneObservedFreeCancelsInnerZero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  let freeLeg := iteratedQuadraticFreeSignedLeg term
  let inner₀ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 0
  let inner₁ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 1
  freeLeg.sign = .phase ∧ inner₀.sign = .conjugate ∧
    inner₁.sign = .phase ∧ inner₁.mode = observed ∧
    freeLeg.mode = inner₀.mode

/-- `free-`, `inner0+`, `inner1+`, with inner zero carrying the observed
copy and inner one cancelling the free leg. -/
def InnerZeroObservedInnerOneCancelsFree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  let freeLeg := iteratedQuadraticFreeSignedLeg term
  let inner₀ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 0
  let inner₁ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 1
  freeLeg.sign = .conjugate ∧ inner₀.sign = .phase ∧
    inner₁.sign = .phase ∧ inner₀.mode = observed ∧
    inner₁.mode = freeLeg.mode

/-- `free-`, `inner0+`, `inner1+`, with inner one carrying the observed
copy and inner zero cancelling the free leg. -/
def InnerOneObservedInnerZeroCancelsFree
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  let freeLeg := iteratedQuadraticFreeSignedLeg term
  let inner₀ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 0
  let inner₁ := adjustedFirstPicardInnerLeg
    (iteratedQuadraticInnerEntry term) 1
  freeLeg.sign = .conjugate ∧ inner₀.sign = .phase ∧
    inner₁.sign = .phase ∧ inner₁.mode = observed ∧
    inner₀.mode = freeLeg.mode

/-- The two channels in which the free outer leg is the observed copy. -/
def MatchedIteratedQuadraticTadpoleChannel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  FreeObservedInnerZeroCancelsInnerOne observed term ∨
    FreeObservedInnerOneCancelsInnerZero observed term

/-- The four channels in which an inner leg is the observed copy. -/
def MatchedIteratedQuadraticConnectedChannel
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  InnerZeroObservedFreeCancelsInnerOne observed term ∨
    InnerOneObservedFreeCancelsInnerZero observed term ∨
    InnerZeroObservedInnerOneCancelsFree observed term ∨
    InnerOneObservedInnerZeroCancelsFree observed term

/-- Full six-way ordered classification of a charge-matched return tree. -/
theorem matchedIteratedQuadratic_six_return_channels
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    FreeObservedInnerZeroCancelsInnerOne observed term ∨
      InnerZeroObservedFreeCancelsInnerOne observed term ∨
      FreeObservedInnerOneCancelsInnerZero observed term ∨
      InnerOneObservedFreeCancelsInnerZero observed term ∨
      InnerZeroObservedInnerOneCancelsFree observed term ∨
      InnerOneObservedInnerZeroCancelsFree observed term := by
  have hclassification :=
    matchedIteratedQuadratic_threeLeg_classification observed term hcharge
  dsimp only at hclassification
  rcases hclassification with hzeroOne | hzeroOne | hzeroOne
  · rcases hzeroOne with ⟨hfree, hinner₀, hinner₁, hpairs⟩
    rcases hpairs with hpairs | hpairs
    · exact Or.inl ⟨hfree, hinner₀, hinner₁, hpairs.1, hpairs.2⟩
    · exact Or.inr (Or.inl
        ⟨hfree, hinner₀, hinner₁, hpairs.1, hpairs.2⟩)
  · rcases hzeroOne with ⟨hfree, hinner₀, hinner₁, hpairs⟩
    rcases hpairs with hpairs | hpairs
    · exact Or.inr (Or.inr (Or.inl
        ⟨hfree, hinner₀, hinner₁, hpairs.1, hpairs.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hfree, hinner₀, hinner₁, hpairs.1, hpairs.2⟩)))
  · rcases hzeroOne with ⟨hfree, hinner₀, hinner₁, hpairs⟩
    rcases hpairs with hpairs | hpairs
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hfree, hinner₀, hinner₁, hpairs.1, hpairs.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hfree, hinner₀, hinner₁, hpairs.1, hpairs.2⟩))))

/-- Every charge-matched tree lies in a tadpole or connected channel.  The
disjunction is intentionally not claimed disjoint when modes coincide. -/
theorem matchedIteratedQuadratic_tadpole_or_connected
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    MatchedIteratedQuadraticTadpoleChannel observed term ∨
      MatchedIteratedQuadraticConnectedChannel observed term := by
  rcases matchedIteratedQuadratic_six_return_channels
      observed term hcharge with h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end

end ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
