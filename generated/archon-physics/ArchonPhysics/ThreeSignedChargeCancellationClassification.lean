import ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
import ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity

/-!
# Classification of three signed charges returning one positive charge

Three signed coordinate unit charges can sum to one prescribed positive unit
charge only in a two-positive/one-negative sector.  The two positive modes are
the prescribed observed mode and the mode of the negative leg, with
multiplicity.  This multiset formulation deliberately retains the all-equal
case, in which more than one positive leg can serve as the observed copy.

The abstract classification is then applied to the three phase legs of a
charge-matched iterated-quadratic second-Picard tree.  No distinct-mode or
frequency hypothesis is used.
-/

namespace ArchonPhysics.ThreeSignedChargeCancellationClassification

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-! ## Abstract three-leg classification -/

/-- A positive signed mode at a prescribed coordinate. -/
def positiveSignedMode {d : Type*} (mode : d) : SignedMode d :=
  ⟨mode, .phase⟩

/-- A negative signed mode at a prescribed coordinate. -/
def negativeSignedMode {d : Type*} (mode : d) : SignedMode d :=
  ⟨mode, .conjugate⟩

@[simp] theorem positiveSignedMode_mode {d : Type*} (mode : d) :
    (positiveSignedMode mode).mode = mode := rfl

@[simp] theorem positiveSignedMode_sign {d : Type*} (mode : d) :
    (positiveSignedMode mode).sign = .phase := rfl

@[simp] theorem negativeSignedMode_mode {d : Type*} (mode : d) :
    (negativeSignedMode mode).mode = mode := rfl

@[simp] theorem negativeSignedMode_sign {d : Type*} (mode : d) :
    (negativeSignedMode mode).sign = .conjugate := rfl

/-- A negative unit charge is the additive inverse of the corresponding
positive unit charge. -/
theorem negativeSignedMode_charge
    {d : Type*} [DecidableEq d] (mode : d) :
    (negativeSignedMode mode).charge =
      -(positiveSignedMode mode).charge := by
  ext coordinate
  simp [negativeSignedMode, positiveSignedMode, SignedMode.charge,
    PhaseSign.exponent, Pi.single_neg]

/-- Summing all coordinates of one signed unit charge recovers its exponent. -/
theorem sum_signedMode_charge
    {d : Type*} [Fintype d] [DecidableEq d] (leg : SignedMode d) :
    (∑ coordinate, leg.charge coordinate) = leg.sign.exponent := by
  classical
  rcases leg with ⟨mode, sign⟩
  unfold SignedMode.charge
  rw [Fintype.sum_eq_single mode]
  · simp
  · intro other hne
    simp [hne]

/-- The sum of two positive unit charges is never zero, including when their
modes coincide. -/
theorem add_positiveSignedMode_charge_ne_zero
    {d : Type*} [DecidableEq d] (left right : d) :
    (positiveSignedMode left).charge +
        (positiveSignedMode right).charge ≠ 0 := by
  intro hzero
  have hatLeft := congrFun hzero left
  by_cases hsame : right = left
  · subst right
    simp [positiveSignedMode, SignedMode.charge, PhaseSign.exponent] at hatLeft
  · simp [positiveSignedMode, SignedMode.charge, PhaseSign.exponent,
      hsame] at hatLeft

/-- The unordered pair of positive modes consists of the observed mode and
the negative-leg mode. -/
def PositivePairMatchesObservedCancel {d : Type*}
    (observed plus₀ plus₁ minus : d) : Prop :=
  (plus₀ = observed ∧ plus₁ = minus) ∨
    (plus₁ = observed ∧ plus₀ = minus)

/-- Abstract classification of three signed coordinate charges.  Exactly one
of the three displayed disjuncts holds at the sign-pattern level; the mode
relation is deliberately unordered to cover repeated and all-equal modes. -/
theorem three_signedMode_charge_eq_positive_classification
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
          leg₁.mode leg₂.mode leg₀.mode) := by
  let _ := Fintype.ofFinite d
  have htotal :
      leg₀.sign.exponent + leg₁.sign.exponent + leg₂.sign.exponent = 1 := by
    have hsum := congrArg
      (fun charge : d → Int ↦ ∑ mode, charge mode) hcharge
    simpa only [Pi.add_apply, Finset.sum_add_distrib,
      sum_signedMode_charge, positiveSignedMode_sign,
      PhaseSign.exponent_phase] using hsum
  rcases leg₀ with ⟨mode₀, sign₀⟩
  rcases leg₁ with ⟨mode₁, sign₁⟩
  rcases leg₂ with ⟨mode₂, sign₂⟩
  cases sign₀ <;> cases sign₁ <;> cases sign₂
  · norm_num [PhaseSign.exponent] at htotal
  · refine Or.inl ⟨rfl, rfl, rfl, ?_⟩
    have hpair :
        (positiveSignedMode mode₀).charge +
            (positiveSignedMode mode₁).charge =
          (positiveSignedMode observed).charge +
            (positiveSignedMode mode₂).charge := by
      change (positiveSignedMode mode₀).charge +
          (positiveSignedMode mode₁).charge +
          (negativeSignedMode mode₂).charge =
        (positiveSignedMode observed).charge at hcharge
      rw [negativeSignedMode_charge mode₂] at hcharge
      linear_combination hcharge
    have hclassified := nonzero_two_signedMode_charge_fiber
      (positiveSignedMode mode₀) (positiveSignedMode mode₁)
      (positiveSignedMode observed) (positiveSignedMode mode₂)
      hpair (add_positiveSignedMode_charge_ne_zero mode₀ mode₁)
    unfold PositivePairMatchesObservedCancel
    rcases hclassified with hsame | hswap
    · left
      exact ⟨(congrArg SignedMode.mode hsame.1).symm,
        (congrArg SignedMode.mode hsame.2).symm⟩
    · right
      exact ⟨(congrArg SignedMode.mode hswap.1).symm,
        (congrArg SignedMode.mode hswap.2).symm⟩
  · refine Or.inr (Or.inl ⟨rfl, rfl, rfl, ?_⟩)
    have hpair :
        (positiveSignedMode mode₀).charge +
            (positiveSignedMode mode₂).charge =
          (positiveSignedMode observed).charge +
            (positiveSignedMode mode₁).charge := by
      change (positiveSignedMode mode₀).charge +
          (negativeSignedMode mode₁).charge +
          (positiveSignedMode mode₂).charge =
        (positiveSignedMode observed).charge at hcharge
      rw [negativeSignedMode_charge mode₁] at hcharge
      linear_combination hcharge
    have hclassified := nonzero_two_signedMode_charge_fiber
      (positiveSignedMode mode₀) (positiveSignedMode mode₂)
      (positiveSignedMode observed) (positiveSignedMode mode₁)
      hpair (add_positiveSignedMode_charge_ne_zero mode₀ mode₂)
    unfold PositivePairMatchesObservedCancel
    rcases hclassified with hsame | hswap
    · left
      exact ⟨(congrArg SignedMode.mode hsame.1).symm,
        (congrArg SignedMode.mode hsame.2).symm⟩
    · right
      exact ⟨(congrArg SignedMode.mode hswap.1).symm,
        (congrArg SignedMode.mode hswap.2).symm⟩
  · norm_num [PhaseSign.exponent] at htotal
  · refine Or.inr (Or.inr ⟨rfl, rfl, rfl, ?_⟩)
    have hpair :
        (positiveSignedMode mode₁).charge +
            (positiveSignedMode mode₂).charge =
          (positiveSignedMode observed).charge +
            (positiveSignedMode mode₀).charge := by
      change (negativeSignedMode mode₀).charge +
          (positiveSignedMode mode₁).charge +
          (positiveSignedMode mode₂).charge =
        (positiveSignedMode observed).charge at hcharge
      rw [negativeSignedMode_charge mode₀] at hcharge
      linear_combination hcharge
    have hclassified := nonzero_two_signedMode_charge_fiber
      (positiveSignedMode mode₁) (positiveSignedMode mode₂)
      (positiveSignedMode observed) (positiveSignedMode mode₀)
      hpair (add_positiveSignedMode_charge_ne_zero mode₁ mode₂)
    unfold PositivePairMatchesObservedCancel
    rcases hclassified with hsame | hswap
    · left
      exact ⟨(congrArg SignedMode.mode hsame.1).symm,
        (congrArg SignedMode.mode hsame.2).symm⟩
    · right
      exact ⟨(congrArg SignedMode.mode hswap.1).symm,
        (congrArg SignedMode.mode hswap.2).symm⟩
  · norm_num [PhaseSign.exponent] at htotal
  · norm_num [PhaseSign.exponent] at htotal
  · norm_num [PhaseSign.exponent] at htotal

/-! ## Adaptation to an iterated-quadratic tree -/

/-- Binary sign in input slot zero or one of a quadratic phase term. -/
def quadraticPhaseTermBinarySign {N : Nat}
    (term : QuadraticPhaseTerm N) (input : Fin 2) : Fin 2 :=
  if input = 0 then term.2.1 else term.2.2

@[simp] theorem quadraticPhaseTermBinarySign_zero {N : Nat}
    (term : QuadraticPhaseTerm N) :
    quadraticPhaseTermBinarySign term 0 = term.2.1 := by
  simp [quadraticPhaseTermBinarySign]

@[simp] theorem quadraticPhaseTermBinarySign_one {N : Nat}
    (term : QuadraticPhaseTerm N) :
    quadraticPhaseTermBinarySign term 1 = term.2.2 := by
  simp [quadraticPhaseTermBinarySign]

/-- The conjugate coordinate branch flips both binary signs of the inner
quadratic term. -/
def coordinateBranchAdjustedBinarySign
    (branch sign : Fin 2) : Fin 2 :=
  if branch = 0 then sign else otherQuadraticSlot sign

@[simp] theorem coordinateBranchAdjustedBinarySign_zero (sign : Fin 2) :
    coordinateBranchAdjustedBinarySign 0 sign = sign := by
  simp [coordinateBranchAdjustedBinarySign]

@[simp] theorem coordinateBranchAdjustedBinarySign_one (sign : Fin 2) :
    coordinateBranchAdjustedBinarySign 1 sign = otherQuadraticSlot sign := by
  simp [coordinateBranchAdjustedBinarySign]

/-- One of the two signed inner legs after applying the positive/conjugate
coordinate branch. -/
def adjustedFirstPicardInnerLeg
    {N : Nat} [NeZero N]
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N)
    (input : Fin 2) : SignedMode (Lattice.Site N) :=
  binarySignedMode (entry.1.1 input)
    (coordinateBranchAdjustedBinarySign entry.2
      (quadraticPhaseTermBinarySign entry.1 input))

/-- The signed free outer leg of an iterated tree. -/
def iteratedQuadraticFreeSignedLeg
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    SignedMode (Lattice.Site N) :=
  binarySignedMode (iteratedQuadraticFreeMode term)
    (iteratedQuadraticFreeSign term)

/-- The coordinate-branch charge is exactly the sum of its two adjusted inner
signed legs. -/
theorem physlibFirstPicardCoordinateCharge_eq_adjustedInnerLegs
    {N : Nat} [NeZero N]
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    physlibQuadraticFirstPicardCoordinateCharacterCharge entry =
      (adjustedFirstPicardInnerLeg entry 0).charge +
        (adjustedFirstPicardInnerLeg entry 1).charge := by
  rcases entry with ⟨⟨modes, sign₀, sign₁⟩, branch⟩
  fin_cases branch <;> fin_cases sign₀ <;> fin_cases sign₁ <;>
    simp [physlibQuadraticFirstPicardCoordinateCharacterCharge,
      twoBranchRealPartCharge, quadraticPhaseCharge,
      adjustedFirstPicardInnerLeg, quadraticPhaseTermBinarySign,
      coordinateBranchAdjustedBinarySign, otherQuadraticSlot,
      binarySignedMode, binaryPhaseSign, SignedMode.charge, Pi.single_neg] <;>
    abel

/-- The total iterated charge is the sum of the free leg and the two adjusted
inner legs. -/
theorem iteratedQuadraticSecondPicardCharge_eq_threeLegs
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardCharge term =
      (iteratedQuadraticFreeSignedLeg term).charge +
        (adjustedFirstPicardInnerLeg
            (iteratedQuadraticInnerEntry term) 0).charge +
        (adjustedFirstPicardInnerLeg
            (iteratedQuadraticInnerEntry term) 1).charge := by
  unfold iteratedQuadraticSecondPicardCharge
    iteratedQuadraticFreeSignedLeg iteratedQuadraticFreeCharge
  rw [physlibFirstPicardCoordinateCharge_eq_adjustedInnerLegs]
  abel

/-- Full three-leg cancellation classification for a charge-matched
iterated-quadratic `Sum.inl` tree. -/
theorem matchedIteratedQuadratic_threeLeg_classification
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
          inner₀.mode inner₁.mode freeLeg.mode) := by
  dsimp only
  apply three_signedMode_charge_eq_positive_classification
  rw [← iteratedQuadraticSecondPicardCharge_eq_threeLegs]
  simpa [positiveSignedMode, freeInitialPhaseCharge, binarySignedMode,
    binaryPhaseSign] using hcharge.symm

end

end ArchonPhysics.ThreeSignedChargeCancellationClassification
