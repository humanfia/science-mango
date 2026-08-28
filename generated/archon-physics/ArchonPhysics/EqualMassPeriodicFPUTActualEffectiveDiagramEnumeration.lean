import ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
import ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex

/-!
# Reindexing the actual first-normal-form feedback by four-wave diagrams

The actual first normal form produces a finite sum with two choices for the
outer insertion slot and four signed nonzero branch modes.  This file first
exposes that sum term by term.  It then records the physical-momentum and
relative-branch relabelling which places the same indices in
`EffectiveFourWaveDiagram`.

This is a finite algebraic interface.  In particular, it distinguishes the
root-phase primitive used by `actualEffectiveCubicFourWaveSource` from the
inner-time primitive used by the older nested-Picard coefficient; no equality
between those two time orderings is silently assumed.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTBranchMomentumRelabel
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.Lattice
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NestedOscillatoryEnergyIdentity
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.QuadraticInteractionFirstNormalForm

noncomputable section

/-! ## Literal two-vertex indices and their exact source term -/

/-- Slot, outer-left, outer-right, inner-left, and inner-right branch modes. -/
abbrev ActualCubicFeedbackIndex (N : Nat) :=
  Fin 2 × (ActualInteractionBranchMode N ×
    (ActualInteractionBranchMode N ×
      (ActualInteractionBranchMode N × ActualInteractionBranchMode N)))

def mkActualCubicFeedbackIndex {N : Nat}
    (slot : Fin 2)
    (outerLeft outerRight innerLeft innerRight : ActualInteractionBranchMode N) :
    ActualCubicFeedbackIndex N :=
  (slot, (outerLeft, (outerRight, (innerLeft, innerRight))))

def feedbackInsertionSlot {N : Nat}
    (index : ActualCubicFeedbackIndex N) : Fin 2 := index.1

def feedbackOuterLeft {N : Nat}
    (index : ActualCubicFeedbackIndex N) : ActualInteractionBranchMode N :=
  index.2.1

def feedbackOuterRight {N : Nat}
    (index : ActualCubicFeedbackIndex N) : ActualInteractionBranchMode N :=
  index.2.2.1

def feedbackInnerLeft {N : Nat}
    (index : ActualCubicFeedbackIndex N) : ActualInteractionBranchMode N :=
  index.2.2.2.1

def feedbackInnerRight {N : Nat}
    (index : ActualCubicFeedbackIndex N) : ActualInteractionBranchMode N :=
  index.2.2.2.2

def feedbackInsertedMode {N : Nat}
    (index : ActualCubicFeedbackIndex N) : ActualInteractionBranchMode N :=
  if feedbackInsertionSlot index = 0 then
    feedbackOuterLeft index
  else feedbackOuterRight index

def feedbackSpectatorMode {N : Nat}
    (index : ActualCubicFeedbackIndex N) : ActualInteractionBranchMode N :=
  if feedbackInsertionSlot index = 0 then
    feedbackOuterRight index
  else feedbackOuterLeft index

/-- One inner instantaneous quadratic source summand. -/
def actualInnerVelocitySummand
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (inserted innerLeft innerRight : ActualInteractionBranchMode N) :
    Complex :=
  actualQuadraticVertex N 1 inserted innerLeft innerRight *
    Complex.exp ((Complex.I * actualQuadraticMismatch N
      inserted innerLeft innerRight) * tau) *
    amplitude innerLeft * amplitude innerRight

/-- One literal term in the product-rule feedback. -/
def actualCubicFeedbackTerm
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) : Complex :=
  actualQuadraticVertex N 1 out
      (feedbackOuterLeft index) (feedbackOuterRight index) *
    oscillatoryIntegral (actualQuadraticMismatch N out
      (feedbackOuterLeft index) (feedbackOuterRight index)) tau *
    if feedbackInsertionSlot index = 0 then
      actualInnerVelocitySummand N amplitude tau
          (feedbackOuterLeft index)
          (feedbackInnerLeft index) (feedbackInnerRight index) *
        amplitude (feedbackOuterRight index)
    else
      amplitude (feedbackOuterLeft index) *
        actualInnerVelocitySummand N amplitude tau
          (feedbackOuterRight index)
          (feedbackInnerLeft index) (feedbackInnerRight index)

/-- The generic cubic feedback is exactly the sum of its literal slot and
four-mode indices. -/
theorem actualEffectiveCubicFourWaveSource_eq_feedbackIndexSum
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    actualEffectiveCubicFourWaveSource N amplitude tau out =
      ∑ index : ActualCubicFeedbackIndex N,
        actualCubicFeedbackTerm N amplitude tau out index := by
  rw [show (∑ index : ActualCubicFeedbackIndex N,
      actualCubicFeedbackTerm N amplitude tau out index) =
      ∑ slot : Fin 2,
        ∑ outerLeft, ∑ outerRight, ∑ innerLeft, ∑ innerRight,
          actualCubicFeedbackTerm N amplitude tau out
            (mkActualCubicFeedbackIndex slot outerLeft outerRight
              innerLeft innerRight) by
    simp only [Fintype.sum_prod_type, mkActualCubicFeedbackIndex]]
  unfold actualEffectiveCubicFourWaveSource
    quadraticCubicNormalFormSource quadraticHistoryFeedback
    quadraticOscillatorySource
  simp only [actualCubicFeedbackTerm, actualInnerVelocitySummand,
    mkActualCubicFeedbackIndex, feedbackOuterLeft, feedbackOuterRight,
    feedbackInnerLeft, feedbackInnerRight, feedbackInsertionSlot,
    Fin.sum_univ_two, Fin.isValue]
  simp only [if_pos, one_ne_zero, if_false]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_add]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib]

/-! ## Relative branches and physical momenta -/

/-- Inverse index for the existing two-element branch enumeration. -/
def phaseSignIndex : PhaseSign → Fin 2
  | .phase => 0
  | .conjugate => 1

@[simp] theorem binaryPhaseSign_phaseSignIndex (sign : PhaseSign) :
    binaryPhaseSign (phaseSignIndex sign) = sign := by
  cases sign <;> simp [phaseSignIndex]

@[simp] theorem phaseSignIndex_binaryPhaseSign (index : Fin 2) :
    phaseSignIndex (binaryPhaseSign index) = index := by
  fin_cases index <;> simp [phaseSignIndex]

def binaryPhaseSignEquiv : Fin 2 ≃ PhaseSign where
  toFun := binaryPhaseSign
  invFun := phaseSignIndex
  left_inv := phaseSignIndex_binaryPhaseSign
  right_inv := binaryPhaseSign_phaseSignIndex

theorem composePhaseSign_self_left
    (sign other : PhaseSign) :
    composePhaseSign sign (composePhaseSign sign other) = other := by
  cases sign <;> cases other <;> rfl

theorem phaseSignedMomentum_self
    {N : Nat} (sign : PhaseSign) (mode : Site N) :
    EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum sign
      (EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum sign mode) =
        mode := by
  cases sign <;>
    simp [EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum]

theorem branchPhaseSignedMomentum_add
    {N : Nat} (sign : PhaseSign) (left right : Site N) :
    EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum sign
        (left + right) =
      EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum sign left +
        EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum sign right := by
  cases sign
  · rfl
  · simp [EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum]
    abel

/-- Physical positive-frequency momentum carried by an actual branch mode. -/
def actualPhysicalMomentum {N : Nat}
    (mode : ActualInteractionBranchMode N) : Site N :=
  EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum
    (actualBranchSign mode) (actualBranchRawMode mode)

theorem actualPhysicalMomentum_ne_zero
    {N : Nat} (mode : ActualInteractionBranchMode N) :
    actualPhysicalMomentum mode ≠ 0 := by
  simp [actualPhysicalMomentum, actualBranchRawMode_ne_zero]

/-- Branch of `mode` relative to the reference/output branch. -/
def relativeActualBranch {N : Nat}
    (reference mode : ActualInteractionBranchMode N) : PhaseSign :=
  composePhaseSign (actualBranchSign reference) (actualBranchSign mode)

/-- A relative branch and its physical momentum determine the actual branch
uniquely once the reference branch is fixed. -/
theorem actualMode_eq_of_relativeBranch_eq_of_physicalMomentum_eq
    {N : Nat} (reference left right : ActualInteractionBranchMode N)
    (hbranch : relativeActualBranch reference left =
      relativeActualBranch reference right)
    (hmomentum : actualPhysicalMomentum left = actualPhysicalMomentum right) :
    left = right := by
  have hsign : actualBranchSign left = actualBranchSign right := by
    have h := congrArg (composePhaseSign (actualBranchSign reference)) hbranch
    simpa [relativeActualBranch, composePhaseSign_self_left] using h
  have hindex : left.1 = right.1 := by
    apply binaryPhaseSignEquiv.injective
    exact hsign
  have hraw : actualBranchRawMode left = actualBranchRawMode right := by
    unfold actualPhysicalMomentum at hmomentum
    rw [← hsign] at hmomentum
    have h := congrArg
      (EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum
        (actualBranchSign left)) hmomentum
    simpa [phaseSignedMomentum_self] using h
  apply Prod.ext hindex
  exact Subtype.ext hraw

/-! ## Explicit map into `EffectiveFourWaveDiagram` -/

def feedbackDiagramBranchIndex {N : Nat}
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) : Fin 4 → Fin 2 :=
  Fin.cons
    (phaseSignIndex (relativeActualBranch out (feedbackInsertedMode index)))
    (Fin.cons
      (phaseSignIndex (relativeActualBranch out (feedbackSpectatorMode index)))
      (Fin.cons
        (phaseSignIndex (relativeActualBranch
          (feedbackInsertedMode index) (feedbackInnerLeft index)))
        (fun _ ↦ phaseSignIndex (relativeActualBranch
          (feedbackInsertedMode index) (feedbackInnerRight index)))))

def feedbackDiagramMode {N : Nat}
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) : Fin 5 → Site N :=
  Fin.cons (actualPhysicalMomentum out)
    (Fin.cons (actualPhysicalMomentum (feedbackInsertedMode index))
      (Fin.cons (actualPhysicalMomentum (feedbackSpectatorMode index))
        (Fin.cons (actualPhysicalMomentum (feedbackInnerLeft index))
          (fun _ ↦ actualPhysicalMomentum (feedbackInnerRight index)))))

/-- The concrete relative-branch/physical-momentum reindexing into the
existing diagram type. -/
def feedbackToEffectiveDiagram {N : Nat}
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) : EffectiveFourWaveDiagram N :=
  (feedbackInsertionSlot index,
    (feedbackDiagramBranchIndex out index, feedbackDiagramMode out index))

@[simp] theorem feedbackToEffectiveDiagram_slot
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    outerInsertionSlot (feedbackToEffectiveDiagram out index) =
      feedbackInsertionSlot index := rfl

@[simp] theorem feedbackToEffectiveDiagram_insertedBranch
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    insertedBranch (feedbackToEffectiveDiagram out index) =
      relativeActualBranch out (feedbackInsertedMode index) := by
  simp [feedbackToEffectiveDiagram, insertedBranch, diagramBranch,
    feedbackDiagramBranchIndex]

@[simp] theorem feedbackToEffectiveDiagram_spectatorBranch
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    spectatorBranch (feedbackToEffectiveDiagram out index) =
      relativeActualBranch out (feedbackSpectatorMode index) := by
  simp [feedbackToEffectiveDiagram, spectatorBranch, diagramBranch,
    feedbackDiagramBranchIndex]

@[simp] theorem feedbackToEffectiveDiagram_innerLeftBranch
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    innerLeftBranch (feedbackToEffectiveDiagram out index) =
      relativeActualBranch (feedbackInsertedMode index)
        (feedbackInnerLeft index) := by
  change binaryPhaseSign (phaseSignIndex (relativeActualBranch
    (feedbackInsertedMode index) (feedbackInnerLeft index))) = _
  exact binaryPhaseSign_phaseSignIndex _

@[simp] theorem feedbackToEffectiveDiagram_innerRightBranch
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    innerRightBranch (feedbackToEffectiveDiagram out index) =
      relativeActualBranch (feedbackInsertedMode index)
        (feedbackInnerRight index) := by
  change binaryPhaseSign (phaseSignIndex (relativeActualBranch
    (feedbackInsertedMode index) (feedbackInnerRight index))) = _
  exact binaryPhaseSign_phaseSignIndex _

@[simp] theorem feedbackToEffectiveDiagram_outputMomentum
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    outputMomentum (feedbackToEffectiveDiagram out index) =
      actualPhysicalMomentum out := rfl

@[simp] theorem feedbackToEffectiveDiagram_intermediateMomentum
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    intermediateMomentum (feedbackToEffectiveDiagram out index) =
      actualPhysicalMomentum (feedbackInsertedMode index) := rfl

@[simp] theorem feedbackToEffectiveDiagram_spectatorMomentum
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    spectatorMomentum (feedbackToEffectiveDiagram out index) =
      actualPhysicalMomentum (feedbackSpectatorMode index) := rfl

@[simp] theorem feedbackToEffectiveDiagram_innerLeftMomentum
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    innerLeftMomentum (feedbackToEffectiveDiagram out index) =
      actualPhysicalMomentum (feedbackInnerLeft index) := rfl

@[simp] theorem feedbackToEffectiveDiagram_innerRightMomentum
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    innerRightMomentum (feedbackToEffectiveDiagram out index) =
      actualPhysicalMomentum (feedbackInnerRight index) := rfl

theorem feedbackToEffectiveDiagram_injective
    {N : Nat} (out : ActualInteractionBranchMode N) :
    Function.Injective (feedbackToEffectiveDiagram out) := by
  intro leftIndex rightIndex heq
  have hslot : feedbackInsertionSlot leftIndex =
      feedbackInsertionSlot rightIndex := by
    exact congrArg outerInsertionSlot heq
  have hinsertedBranch : relativeActualBranch out
      (feedbackInsertedMode leftIndex) =
      relativeActualBranch out (feedbackInsertedMode rightIndex) := by
    have h := congrArg insertedBranch heq
    simpa using h
  have hinsertedMomentum : actualPhysicalMomentum
      (feedbackInsertedMode leftIndex) =
      actualPhysicalMomentum (feedbackInsertedMode rightIndex) := by
    have h := congrArg intermediateMomentum heq
    simpa using h
  have hinserted : feedbackInsertedMode leftIndex =
      feedbackInsertedMode rightIndex :=
    actualMode_eq_of_relativeBranch_eq_of_physicalMomentum_eq
      out _ _ hinsertedBranch hinsertedMomentum
  have hspectatorBranch : relativeActualBranch out
      (feedbackSpectatorMode leftIndex) =
      relativeActualBranch out (feedbackSpectatorMode rightIndex) := by
    have h := congrArg spectatorBranch heq
    simpa using h
  have hspectatorMomentum : actualPhysicalMomentum
      (feedbackSpectatorMode leftIndex) =
      actualPhysicalMomentum (feedbackSpectatorMode rightIndex) := by
    have h := congrArg spectatorMomentum heq
    simpa using h
  have hspectator : feedbackSpectatorMode leftIndex =
      feedbackSpectatorMode rightIndex :=
    actualMode_eq_of_relativeBranch_eq_of_physicalMomentum_eq
      out _ _ hspectatorBranch hspectatorMomentum
  have hinnerLeftBranch : relativeActualBranch
      (feedbackInsertedMode leftIndex) (feedbackInnerLeft leftIndex) =
      relativeActualBranch
        (feedbackInsertedMode rightIndex) (feedbackInnerLeft rightIndex) := by
    have h := congrArg innerLeftBranch heq
    simpa using h
  have hinnerLeftMomentum : actualPhysicalMomentum
      (feedbackInnerLeft leftIndex) =
      actualPhysicalMomentum (feedbackInnerLeft rightIndex) := by
    have h := congrArg innerLeftMomentum heq
    simpa using h
  have hinnerLeft : feedbackInnerLeft leftIndex =
      feedbackInnerLeft rightIndex := by
    rw [hinserted] at hinnerLeftBranch
    exact actualMode_eq_of_relativeBranch_eq_of_physicalMomentum_eq
      (feedbackInsertedMode rightIndex) _ _
      hinnerLeftBranch hinnerLeftMomentum
  have hinnerRightBranch : relativeActualBranch
      (feedbackInsertedMode leftIndex) (feedbackInnerRight leftIndex) =
      relativeActualBranch
        (feedbackInsertedMode rightIndex) (feedbackInnerRight rightIndex) := by
    have h := congrArg innerRightBranch heq
    simpa using h
  have hinnerRightMomentum : actualPhysicalMomentum
      (feedbackInnerRight leftIndex) =
      actualPhysicalMomentum (feedbackInnerRight rightIndex) := by
    have h := congrArg innerRightMomentum heq
    simpa using h
  have hinnerRight : feedbackInnerRight leftIndex =
      feedbackInnerRight rightIndex := by
    rw [hinserted] at hinnerRightBranch
    exact actualMode_eq_of_relativeBranch_eq_of_physicalMomentum_eq
      (feedbackInsertedMode rightIndex) _ _
      hinnerRightBranch hinnerRightMomentum
  rcases leftIndex with ⟨leftSlot, leftOuterLeft, leftOuterRight,
    leftInnerLeft, leftInnerRight⟩
  rcases rightIndex with ⟨rightSlot, rightOuterLeft, rightOuterRight,
    rightInnerLeft, rightInnerRight⟩
  change leftSlot = rightSlot at hslot
  change leftInnerLeft = rightInnerLeft at hinnerLeft
  change leftInnerRight = rightInnerRight at hinnerRight
  subst rightSlot
  fin_cases leftSlot
  all_goals
    simp [feedbackInsertedMode, feedbackSpectatorMode,
      feedbackInsertionSlot, feedbackOuterLeft,
      feedbackOuterRight] at hinserted hspectator
    subst_vars
    rfl

theorem effectivePhaseSignedMomentum_relative_actualPhysical
    {N : Nat} (reference mode : ActualInteractionBranchMode N) :
    EqualMassPeriodicFPUTEffectiveFourWaveVertex.phaseSignedMomentum
        (relativeActualBranch reference mode) (actualPhysicalMomentum mode) =
      EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum
        (actualBranchSign reference) (actualBranchRawMode mode) := by
  rcases reference with ⟨referenceSign, referenceMode⟩
  rcases mode with ⟨modeSign, modeValue⟩
  fin_cases referenceSign <;> fin_cases modeSign <;>
    simp [relativeActualBranch, actualPhysicalMomentum, actualBranchSign,
      actualBranchRawMode, binaryPhaseSign, composePhaseSign,
      EqualMassPeriodicFPUTEffectiveFourWaveVertex.phaseSignedMomentum,
      EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum]

theorem feedbackInserted_add_spectator_raw
    {N : Nat} (index : ActualCubicFeedbackIndex N) :
    actualBranchRawMode (feedbackInsertedMode index) +
        actualBranchRawMode (feedbackSpectatorMode index) =
      actualBranchRawMode (feedbackOuterLeft index) +
        actualBranchRawMode (feedbackOuterRight index) := by
  rcases index with ⟨slot, outerLeft, outerRight, innerLeft, innerRight⟩
  fin_cases slot
  · simp [feedbackInsertedMode, feedbackSpectatorMode,
      feedbackInsertionSlot, feedbackOuterLeft, feedbackOuterRight]
  · simp [feedbackInsertedMode, feedbackSpectatorMode,
      feedbackInsertionSlot, feedbackOuterLeft, feedbackOuterRight]
    abel

/-- Both literal quadratic vertices represented by an actual feedback
index obey their raw convolution selectors. -/
def IsActiveActualCubicFeedback
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) : Prop :=
  ActualQuadraticMomentumSupported out
      (feedbackOuterLeft index) (feedbackOuterRight index) ∧
    ActualQuadraticMomentumSupported (feedbackInsertedMode index)
      (feedbackInnerLeft index) (feedbackInnerRight index)

instance isActiveActualCubicFeedbackDecidable
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    Decidable (IsActiveActualCubicFeedback out index) := by
  unfold IsActiveActualCubicFeedback
  infer_instance

abbrev ActiveActualCubicFeedback
    (N : Nat) (out : ActualInteractionBranchMode N) :=
  {index : ActualCubicFeedbackIndex N //
    IsActiveActualCubicFeedback out index}

noncomputable instance activeActualCubicFeedbackFintype
    (N : Nat) [NeZero N] (out : ActualInteractionBranchMode N) :
    Fintype (ActiveActualCubicFeedback N out) :=
  Fintype.ofFinite _

/-- Every feedback index outside the two literal convolution shells has a
zero outer or inner actual vertex. -/
theorem actualCubicFeedbackTerm_eq_zero_of_not_active
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hinactive : ¬ IsActiveActualCubicFeedback out index) :
    actualCubicFeedbackTerm N amplitude tau out index = 0 := by
  by_cases houter : ActualQuadraticMomentumSupported out
      (feedbackOuterLeft index) (feedbackOuterRight index)
  · have hinner : ¬ ActualQuadraticMomentumSupported
        (feedbackInsertedMode index)
        (feedbackInnerLeft index) (feedbackInnerRight index) := by
      intro hinner
      exact hinactive ⟨houter, hinner⟩
    by_cases hslot : feedbackInsertionSlot index = 0
    · have hinnerLeft : ¬ ActualQuadraticMomentumSupported
          (feedbackOuterLeft index)
          (feedbackInnerLeft index) (feedbackInnerRight index) := by
        simpa [feedbackInsertedMode, hslot] using hinner
      simp [actualCubicFeedbackTerm, actualInnerVelocitySummand,
        actualQuadraticVertex, hslot, houter, hinnerLeft]
    · have hinnerRight : ¬ ActualQuadraticMomentumSupported
          (feedbackOuterRight index)
          (feedbackInnerLeft index) (feedbackInnerRight index) := by
        simpa [feedbackInsertedMode, hslot] using hinner
      simp [actualCubicFeedbackTerm, actualInnerVelocitySummand,
        actualQuadraticVertex, hslot, houter, hinnerRight]
  · unfold actualCubicFeedbackTerm
    simp [actualQuadraticVertex, houter]

/-- Consequently the literal feedback sum may be restricted exactly to
active actual two-vertex indices. -/
theorem actualEffectiveCubicFourWaveSource_eq_activeFeedbackSum
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    actualEffectiveCubicFourWaveSource N amplitude tau out =
      ∑ index : ActiveActualCubicFeedback N out,
        actualCubicFeedbackTerm N amplitude tau out index.1 := by
  rw [actualEffectiveCubicFourWaveSource_eq_feedbackIndexSum]
  calc
    (∑ index : ActualCubicFeedbackIndex N,
        actualCubicFeedbackTerm N amplitude tau out index) =
      ∑ index : ActualCubicFeedbackIndex N,
        if IsActiveActualCubicFeedback out index then
          actualCubicFeedbackTerm N amplitude tau out index
        else 0 := by
      apply Finset.sum_congr rfl
      intro index _hindex
      by_cases hactive : IsActiveActualCubicFeedback out index
      · simp [hactive]
      · simp [hactive,
          actualCubicFeedbackTerm_eq_zero_of_not_active
            N amplitude tau out index hactive]
    _ = ∑ index : ActiveActualCubicFeedback N out,
        actualCubicFeedbackTerm N amplitude tau out index.1 := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        (Finset.univ.filter (IsActiveActualCubicFeedback out))
        (by intro index; simp) _

/-- Active actual feedback indices land in the exact two-vertex momentum
shell of the existing effective diagram. -/
theorem feedbackToEffectiveDiagram_momentumSupported
    {N : Nat} (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    IsTwoVertexMomentumSupported (feedbackToEffectiveDiagram out index) := by
  constructor
  · simp only [feedbackToEffectiveDiagram_outputMomentum,
      feedbackToEffectiveDiagram_insertedBranch,
      feedbackToEffectiveDiagram_intermediateMomentum,
      feedbackToEffectiveDiagram_spectatorBranch,
      feedbackToEffectiveDiagram_spectatorMomentum]
    rw [effectivePhaseSignedMomentum_relative_actualPhysical,
      effectivePhaseSignedMomentum_relative_actualPhysical]
    unfold actualPhysicalMomentum
    rw [← branchPhaseSignedMomentum_add]
    apply congrArg
      (EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum
        (actualBranchSign out))
    exact hactive.1.trans (feedbackInserted_add_spectator_raw index).symm
  · simp only [feedbackToEffectiveDiagram_intermediateMomentum,
      feedbackToEffectiveDiagram_innerLeftBranch,
      feedbackToEffectiveDiagram_innerLeftMomentum,
      feedbackToEffectiveDiagram_innerRightBranch,
      feedbackToEffectiveDiagram_innerRightMomentum]
    rw [effectivePhaseSignedMomentum_relative_actualPhysical,
      effectivePhaseSignedMomentum_relative_actualPhysical]
    unfold actualPhysicalMomentum
    rw [← branchPhaseSignedMomentum_add]
    exact congrArg
      (EqualMassPeriodicFPUTBranchMomentumRelabel.phaseSignedMomentum
        (actualBranchSign (feedbackInsertedMode index))) hactive.2

/-- Because the actual mode type already excludes translation modes, an
active actual feedback index maps to the existing active diagram subtype. -/
theorem feedbackToEffectiveDiagram_active
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    IsActiveEffectiveFourWaveDiagram (feedbackToEffectiveDiagram out index) := by
  constructor
  · exact feedbackToEffectiveDiagram_momentumSupported out index hactive
  · intro slot
    fin_cases slot
    · exact actualPhysicalMomentum_ne_zero out
    · exact actualPhysicalMomentum_ne_zero (feedbackInsertedMode index)
    · exact actualPhysicalMomentum_ne_zero (feedbackSpectatorMode index)
    · exact actualPhysicalMomentum_ne_zero (feedbackInnerLeft index)
    · exact actualPhysicalMomentum_ne_zero (feedbackInnerRight index)

/-- The active version of the explicit map lands directly in the pre-existing
`ActiveEffectiveFourWaveDiagram` type. -/
def activeFeedbackToEffectiveDiagram
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActiveActualCubicFeedback N out) :
    ActiveEffectiveFourWaveDiagram N :=
  ⟨feedbackToEffectiveDiagram out index.1,
    feedbackToEffectiveDiagram_active out index.1 index.2⟩

theorem activeFeedbackToEffectiveDiagram_injective
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N) :
    Function.Injective (activeFeedbackToEffectiveDiagram out) := by
  intro left right heq
  apply Subtype.ext
  apply feedbackToEffectiveDiagram_injective out
  exact congrArg Subtype.val heq

abbrev ActiveFeedbackEffectiveDiagramImage
    (N : Nat) [NeZero N] (out : ActualInteractionBranchMode N) :=
  Set.range (activeFeedbackToEffectiveDiagram out)

def activeFeedbackEffectiveDiagramEquiv
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N) :
    ActiveActualCubicFeedback N out ≃
      ActiveFeedbackEffectiveDiagramImage N out :=
  Equiv.ofInjective (activeFeedbackToEffectiveDiagram out)
    (activeFeedbackToEffectiveDiagram_injective out)

noncomputable instance activeFeedbackEffectiveDiagramImageFintype
    (N : Nat) [NeZero N] (out : ActualInteractionBranchMode N) :
    Fintype (ActiveFeedbackEffectiveDiagramImage N out) :=
  Fintype.ofEquiv (ActiveActualCubicFeedback N out)
    (activeFeedbackEffectiveDiagramEquiv out)

def actualActiveEffectiveDiagramTerm
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Complex :=
  actualCubicFeedbackTerm N amplitude tau out
    ((activeFeedbackEffectiveDiagramEquiv out).symm diagram).1

@[simp] theorem actualActiveEffectiveDiagramTerm_equiv
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N)
    (index : ActiveActualCubicFeedback N out) :
    actualActiveEffectiveDiagramTerm N amplitude tau out
        (activeFeedbackEffectiveDiagramEquiv out index) =
      actualCubicFeedbackTerm N amplitude tau out index.1 := by
  simp [actualActiveEffectiveDiagramTerm]

/-- Strong active form of the whole-sum interface: no inactive diagram is
retained, and the target is literally a range subtype of the existing active
effective-diagram type. -/
theorem actualEffectiveCubicFourWaveSource_eq_activeEffectiveDiagramSum
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    actualEffectiveCubicFourWaveSource N amplitude tau out =
      ∑ diagram : ActiveFeedbackEffectiveDiagramImage N out,
        actualActiveEffectiveDiagramTerm N amplitude tau out diagram := by
  rw [actualEffectiveCubicFourWaveSource_eq_activeFeedbackSum]
  calc
    (∑ index : ActiveActualCubicFeedback N out,
        actualCubicFeedbackTerm N amplitude tau out index.1) =
      ∑ index : ActiveActualCubicFeedback N out,
        actualActiveEffectiveDiagramTerm N amplitude tau out
          (activeFeedbackEffectiveDiagramEquiv out index) := by
        apply Finset.sum_congr rfl
        intro index _hindex
        rw [actualActiveEffectiveDiagramTerm_equiv]
    _ = ∑ diagram : ActiveFeedbackEffectiveDiagramImage N out,
        actualActiveEffectiveDiagramTerm N amplitude tau out diagram :=
      Equiv.sum_comp (activeFeedbackEffectiveDiagramEquiv out)
        (actualActiveEffectiveDiagramTerm N amplitude tau out)

/-! ## Exact mismatch identification, including the output conjugation -/

@[simp] theorem periodicSineFrequency_actualPhysicalMomentum
    (N : Nat) [NeZero N] (mode : ActualInteractionBranchMode N) :
    periodicSineFrequency N (actualPhysicalMomentum mode) =
      periodicSineFrequency N (actualBranchRawMode mode) := by
  unfold actualPhysicalMomentum
  exact periodicSineFrequency_phaseSignedMomentum
    N (actualBranchSign mode) (actualBranchRawMode mode)

theorem phaseSignReal_mul_self (sign : PhaseSign) :
    phaseSignReal sign * phaseSignReal sign = 1 := by
  cases sign <;> norm_num

theorem relativeActualBranch_exponent_real
    {N : Nat} (reference mode : ActualInteractionBranchMode N) :
    ((relativeActualBranch reference mode).exponent : Real) =
      phaseSignReal (actualBranchSign reference) *
        phaseSignReal (actualBranchSign mode) := by
  simp only [relativeActualBranch, PhaseSign.exponent_compose]
  unfold phaseSignReal
  push_cast
  rfl

/-- The actual outer/root mismatch is the existing diagram outer mismatch,
with precisely the global output-branch sign accounting for conjugation. -/
theorem outputSign_mul_outerThreeWaveMismatch_eq_actual
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (houter : ActualQuadraticMomentumSupported out
      (feedbackOuterLeft index) (feedbackOuterRight index)) :
    phaseSignReal (actualBranchSign out) *
        outerThreeWaveMismatch (feedbackToEffectiveDiagram out index) =
      actualQuadraticMismatch N out
        (feedbackOuterLeft index) (feedbackOuterRight index) := by
  rw [outerThreeWaveMismatch_eq_explicit]
  simp only [feedbackToEffectiveDiagram_outputMomentum,
    feedbackToEffectiveDiagram_insertedBranch,
    feedbackToEffectiveDiagram_intermediateMomentum,
    feedbackToEffectiveDiagram_spectatorBranch,
    feedbackToEffectiveDiagram_spectatorMomentum,
    periodicSineFrequency_actualPhysicalMomentum,
    relativeActualBranch_exponent_real]
  rw [actualQuadraticMismatch_eq_of_supported houter]
  unfold equalMassQuadraticBranchMismatch
  simp_rw [equalMassFourierFrequency_eq_periodicSineFrequency]
  rw [← rightRawMode_eq_output_sub_left_of_supported houter]
  rcases index with ⟨slot, outerLeft, outerRight, innerLeft, innerRight⟩
  generalize actualBranchSign out = outputSign
  cases outputSign <;> fin_cases slot <;>
    simp [feedbackInsertedMode, feedbackSpectatorMode,
      feedbackInsertionSlot, feedbackOuterLeft, feedbackOuterRight,
      phaseSignReal] <;> ring

/-- Likewise the actual mismatch of the inserted evolution is the existing
inner homological divisor, with the same global output conjugation. -/
theorem outputSign_mul_innerHomologicalDivisor_eq_actual
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hinner : ActualQuadraticMomentumSupported (feedbackInsertedMode index)
      (feedbackInnerLeft index) (feedbackInnerRight index)) :
    phaseSignReal (actualBranchSign out) *
        innerHomologicalDivisor (feedbackToEffectiveDiagram out index) =
      actualQuadraticMismatch N (feedbackInsertedMode index)
        (feedbackInnerLeft index) (feedbackInnerRight index) := by
  unfold innerHomologicalDivisor phaseSignActReal
  rw [innerThreeWaveMismatch_eq_explicit]
  simp only [feedbackToEffectiveDiagram_insertedBranch,
    feedbackToEffectiveDiagram_intermediateMomentum,
    feedbackToEffectiveDiagram_innerLeftBranch,
    feedbackToEffectiveDiagram_innerLeftMomentum,
    feedbackToEffectiveDiagram_innerRightBranch,
    feedbackToEffectiveDiagram_innerRightMomentum,
    periodicSineFrequency_actualPhysicalMomentum,
    relativeActualBranch_exponent_real]
  rw [actualQuadraticMismatch_eq_of_supported hinner]
  unfold equalMassQuadraticBranchMismatch
  simp_rw [equalMassFourierFrequency_eq_periodicSineFrequency]
  rw [← rightRawMode_eq_output_sub_left_of_supported hinner]
  generalize actualBranchSign out = outputSign
  generalize actualBranchSign (feedbackInsertedMode index) = insertedSign
  cases outputSign <;> cases insertedSign <;> simp [phaseSignReal] <;> ring

/-- On active feedback indices the sum of actual root and inserted
mismatches is the globally signed existing total four-wave mismatch. -/
theorem actualOuter_add_innerMismatch_eq_outputSign_mul_totalFourWaveMismatch
    {N : Nat} [NeZero N] (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    actualQuadraticMismatch N out
          (feedbackOuterLeft index) (feedbackOuterRight index) +
        actualQuadraticMismatch N (feedbackInsertedMode index)
          (feedbackInnerLeft index) (feedbackInnerRight index) =
      phaseSignReal (actualBranchSign out) *
        totalFourWaveMismatch (feedbackToEffectiveDiagram out index) := by
  rw [← outer_add_innerHomologicalDivisor_eq_totalFourWaveMismatch]
  rw [mul_add,
    outputSign_mul_outerThreeWaveMismatch_eq_actual out index hactive.1,
    outputSign_mul_innerHomologicalDivisor_eq_actual out index hactive.2]

/-! ## The genuine remaining time-order distinction -/

/-- Time factor in one actual first-normal-form feedback term: the root
mismatch is integrated, while the inserted mismatch is instantaneous. -/
def actualRootedFeedbackTimeKernel
    (N : Nat) [NeZero N] (tau : Real)
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) : Complex :=
  oscillatoryIntegral (actualQuadraticMismatch N out
      (feedbackOuterLeft index) (feedbackOuterRight index)) tau *
    Complex.exp ((Complex.I * actualQuadraticMismatch N
      (feedbackInsertedMode index)
      (feedbackInnerLeft index) (feedbackInnerRight index)) * tau)

/-- On an active index this is exactly the diagram root mismatch and inner
homological divisor, both acted on by the global output sign. -/
theorem actualRootedFeedbackTimeKernel_eq_diagramMismatches
    {N : Nat} [NeZero N] (tau : Real)
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index) :
    actualRootedFeedbackTimeKernel N tau out index =
      oscillatoryIntegral
          (phaseSignReal (actualBranchSign out) *
            outerThreeWaveMismatch (feedbackToEffectiveDiagram out index)) tau *
        Complex.exp ((Complex.I *
          (phaseSignReal (actualBranchSign out) *
            innerHomologicalDivisor (feedbackToEffectiveDiagram out index))) * tau) := by
  unfold actualRootedFeedbackTimeKernel
  rw [← outputSign_mul_outerThreeWaveMismatch_eq_actual
      out index hactive.1,
    ← outputSign_mul_innerHomologicalDivisor_eq_actual
      out index hactive.2]
  push_cast
  rfl

/-- Integrating the actual instantaneous feedback produces the *swapped*
nested coefficient: inserted phase first, root primitive second. -/
theorem hasDerivAt_swappedNestedDiagramKernel
    {N : Nat} [NeZero N]
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N)
    (hactive : IsActiveActualCubicFeedback out index)
    (tau : Real) :
    HasDerivAt
      (nestedOscillatoryIntegral
        (phaseSignReal (actualBranchSign out) *
          innerHomologicalDivisor (feedbackToEffectiveDiagram out index))
        (phaseSignReal (actualBranchSign out) *
          outerThreeWaveMismatch (feedbackToEffectiveDiagram out index)))
      (actualRootedFeedbackTimeKernel N tau out index) tau := by
  have hderiv := hasDerivAt_nestedOscillatoryIntegral
    (phaseSignReal (actualBranchSign out) *
      innerHomologicalDivisor (feedbackToEffectiveDiagram out index))
    (phaseSignReal (actualBranchSign out) *
      outerThreeWaveMismatch (feedbackToEffectiveDiagram out index)) tau
  apply hderiv.congr_deriv
  rw [actualRootedFeedbackTimeKernel_eq_diagramMismatches
    tau out index hactive]
  push_cast
  ring

/-- The rooted and older inner-first time orderings are related by the exact
shuffle identity, not by an unproved equality.  This theorem records the
precise finite correction needed before identifying the old
`effectiveFourWaveCoefficient` representation. -/
theorem rooted_add_innerFirst_nestedDiagramKernel
    {N : Nat} [NeZero N] (tau : Real)
    (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    nestedOscillatoryIntegral
        (phaseSignReal (actualBranchSign out) *
          innerHomologicalDivisor (feedbackToEffectiveDiagram out index))
        (phaseSignReal (actualBranchSign out) *
          outerThreeWaveMismatch (feedbackToEffectiveDiagram out index)) tau +
      nestedOscillatoryIntegral
        (phaseSignReal (actualBranchSign out) *
          outerThreeWaveMismatch (feedbackToEffectiveDiagram out index))
        (phaseSignReal (actualBranchSign out) *
          innerHomologicalDivisor (feedbackToEffectiveDiagram out index)) tau =
      oscillatoryIntegral
          (phaseSignReal (actualBranchSign out) *
            innerHomologicalDivisor (feedbackToEffectiveDiagram out index)) tau *
        oscillatoryIntegral
          (phaseSignReal (actualBranchSign out) *
            outerThreeWaveMismatch (feedbackToEffectiveDiagram out index)) tau :=
  nestedOscillatoryIntegral_add_swap _ _ tau

/-! ## Bijection and pointwise/whole-sum equality -/

/-- The exact subset of existing effective diagrams reached by a fixed
actual output branch.  The range condition is explicit and carries no
dynamical or statistical hypothesis. -/
abbrev FeedbackEffectiveDiagramImage
    (N : Nat) (out : ActualInteractionBranchMode N) :=
  Set.range (feedbackToEffectiveDiagram out)

def feedbackEffectiveDiagramEquiv
    {N : Nat} (out : ActualInteractionBranchMode N) :
    ActualCubicFeedbackIndex N ≃ FeedbackEffectiveDiagramImage N out :=
  Equiv.ofInjective (feedbackToEffectiveDiagram out)
    (feedbackToEffectiveDiagram_injective out)

noncomputable instance feedbackEffectiveDiagramImageFintype
    (N : Nat) [NeZero N] (out : ActualInteractionBranchMode N) :
    Fintype (FeedbackEffectiveDiagramImage N out) :=
  Fintype.ofEquiv (ActualCubicFeedbackIndex N)
    (feedbackEffectiveDiagramEquiv out)

/-- The actual rooted-normal-form term, now indexed by an existing
`EffectiveFourWaveDiagram` together with the transparent range proof. -/
def actualRootedEffectiveDiagramTerm
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N)
    (diagram : FeedbackEffectiveDiagramImage N out) : Complex :=
  actualCubicFeedbackTerm N amplitude tau out
    ((feedbackEffectiveDiagramEquiv out).symm diagram)

/-- Pointwise equality under the explicit reindexing bijection. -/
@[simp] theorem actualRootedEffectiveDiagramTerm_equiv
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N)
    (index : ActualCubicFeedbackIndex N) :
    actualRootedEffectiveDiagramTerm N amplitude tau out
        (feedbackEffectiveDiagramEquiv out index) =
      actualCubicFeedbackTerm N amplitude tau out index := by
  simp [actualRootedEffectiveDiagramTerm]

/-- Whole-sum equality: the actual effective cubic/four-wave source is
literally the finite enumeration over the corresponding range of
`EffectiveFourWaveDiagram`. -/
theorem actualEffectiveCubicFourWaveSource_eq_effectiveDiagramSum
    (N : Nat) [NeZero N]
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    actualEffectiveCubicFourWaveSource N amplitude tau out =
      ∑ diagram : FeedbackEffectiveDiagramImage N out,
        actualRootedEffectiveDiagramTerm N amplitude tau out diagram := by
  rw [actualEffectiveCubicFourWaveSource_eq_feedbackIndexSum]
  calc
    (∑ index : ActualCubicFeedbackIndex N,
        actualCubicFeedbackTerm N amplitude tau out index) =
      ∑ index : ActualCubicFeedbackIndex N,
        actualRootedEffectiveDiagramTerm N amplitude tau out
          (feedbackEffectiveDiagramEquiv out index) := by
        apply Finset.sum_congr rfl
        intro index _hindex
        rw [actualRootedEffectiveDiagramTerm_equiv]
    _ = ∑ diagram : FeedbackEffectiveDiagramImage N out,
        actualRootedEffectiveDiagramTerm N amplitude tau out diagram :=
      Equiv.sum_comp (feedbackEffectiveDiagramEquiv out)
        (actualRootedEffectiveDiagramTerm N amplitude tau out)

end

end ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
