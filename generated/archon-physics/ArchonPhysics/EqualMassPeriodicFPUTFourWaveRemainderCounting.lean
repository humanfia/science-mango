import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoSignatureClassification
import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
import ArchonPhysics.FreeFPUTBinaryTreeMomentumFiberCounting

/-!
# Fixed-output counting of four-wave classification remainders

For a fixed output momentum, an actual supported two-vertex effective FPUT
diagram has two freely chosen inner leaf momenta.  The intermediate and
spectator momenta are then forced by the two exact convolution selectors.
Including the two insertion slots and sixteen branch decorations gives the
explicit upper bound `32 * N^2`.

This module also closes two rigorous lower-dimensional pieces of the
classification remainder:

* actual diagrams whose two inner leaves coincide have cardinal at most
  `32 * N` (and the opposite-sign cancellation subclass inherits this bound);
* on the complete fixed-output `2 ↔ 2` momentum shell, every repeated external
  mode lies on one of four graph lines, hence the whole repeated/cancelling
  shell has cardinal at most `4 * N`, versus the exact shell size `N^2`.

Finally, the one-positive/three-negative sign sector is kept separate and is
shown to have no nonzero acoustic resonance by iterating the already proved
strict three-wave subadditivity theorem.

The adapter from every presented effective diagram to a chosen ordering of
the `2 ↔ 2` shell is not asserted here; presentations are only defined up to
leg permutation.  Thus the `4 * N` theorem is a complete shell count, while
the actual-diagram `32 * N` theorem is presently for the explicit inner-leaf
repeated/cancellation subclass.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTFourWaveRemainderCounting

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveHaarPhaseCouples
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoSignatureClassification
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch

noncomputable section

/-! ## Actual fixed-output supported diagrams -/

/-- Supported effective diagrams with one prescribed output momentum. -/
abbrev FixedOutputSupportedEffectiveFourWaveDiagram
    (N : Nat) [NeZero N] (output : Site N) :=
  {diagram : EffectiveFourWaveDiagram N //
    IsTwoVertexMomentumSupported diagram ∧
      outputMomentum diagram = output}

noncomputable instance fixedOutputSupportedEffectiveFourWaveDiagramFintype
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype (FixedOutputSupportedEffectiveFourWaveDiagram N output) :=
  Fintype.ofFinite _

/-- Two discrete decorations and the two free inner leaf momenta. -/
abbrev FixedOutputTwoVertexParameter (N : Nat) :=
  Fin 2 × ((Fin 4 → Fin 2) × (Site N × Site N))

/-- Forget the forced intermediate and spectator momenta. -/
def fixedOutputTwoVertexParameter
    {N : Nat} [NeZero N] {output : Site N}
    (diagram : FixedOutputSupportedEffectiveFourWaveDiagram N output) :
    FixedOutputTwoVertexParameter N :=
  (outerInsertionSlot diagram.1,
    (diagram.1.2.1,
      (innerLeftMomentum diagram.1, innerRightMomentum diagram.1)))

/-- Multiplication of a lattice momentum by a phase/conjugate sign is
injective. -/
theorem phaseSignedMomentum_injective
    {N : Nat} (sign : PhaseSign) :
    Function.Injective (phaseSignedMomentum (N := N) sign) := by
  cases sign
  · exact Function.injective_id
  · exact neg_injective

/-- At fixed output, the two leaf momenta and discrete decorations determine
the complete supported diagram. -/
theorem fixedOutputTwoVertexParameter_injective
    {N : Nat} [NeZero N] {output : Site N} :
    Function.Injective
      (fixedOutputTwoVertexParameter (N := N) (output := output)) := by
  intro left right hparameter
  have hslot : outerInsertionSlot left.1 = outerInsertionSlot right.1 :=
    congrArg (fun parameter ↦ parameter.1) hparameter
  have hbranches : left.1.2.1 = right.1.2.1 :=
    congrArg (fun parameter ↦ parameter.2.1) hparameter
  have hinnerLeft : innerLeftMomentum left.1 = innerLeftMomentum right.1 :=
    congrArg (fun parameter ↦ parameter.2.2.1) hparameter
  have hinnerRight : innerRightMomentum left.1 = innerRightMomentum right.1 :=
    congrArg (fun parameter ↦ parameter.2.2.2) hparameter
  have hbranch : ∀ branchSlot : Fin 4,
      diagramBranch left.1 branchSlot = diagramBranch right.1 branchSlot := by
    intro branchSlot
    unfold diagramBranch
    rw [hbranches]
  have hinsertedBranch : insertedBranch left.1 = insertedBranch right.1 :=
    hbranch 0
  have hspectatorBranch : spectatorBranch left.1 = spectatorBranch right.1 :=
    hbranch 1
  have hinnerLeftBranch : innerLeftBranch left.1 = innerLeftBranch right.1 :=
    hbranch 2
  have hinnerRightBranch : innerRightBranch left.1 = innerRightBranch right.1 :=
    hbranch 3
  have houtput : outputMomentum left.1 = outputMomentum right.1 := by
    rw [left.2.2, right.2.2]
  have hintermediate :
      intermediateMomentum left.1 = intermediateMomentum right.1 := by
    calc
      intermediateMomentum left.1 =
          phaseSignedMomentum (innerLeftBranch left.1)
              (innerLeftMomentum left.1) +
            phaseSignedMomentum (innerRightBranch left.1)
              (innerRightMomentum left.1) := left.2.1.2
      _ = phaseSignedMomentum (innerLeftBranch right.1)
              (innerLeftMomentum right.1) +
            phaseSignedMomentum (innerRightBranch right.1)
              (innerRightMomentum right.1) := by
        rw [hinnerLeftBranch, hinnerRightBranch,
          hinnerLeft, hinnerRight]
      _ = intermediateMomentum right.1 := right.2.1.2.symm
  have hsignedSpectator :
      phaseSignedMomentum (spectatorBranch left.1)
          (spectatorMomentum left.1) =
        phaseSignedMomentum (spectatorBranch right.1)
          (spectatorMomentum right.1) := by
    calc
      phaseSignedMomentum (spectatorBranch left.1)
          (spectatorMomentum left.1) =
        outputMomentum left.1 -
          phaseSignedMomentum (insertedBranch left.1)
            (intermediateMomentum left.1) := by
          rw [left.2.1.1]
          abel
      _ = outputMomentum right.1 -
          phaseSignedMomentum (insertedBranch right.1)
            (intermediateMomentum right.1) := by
        rw [houtput, hinsertedBranch, hintermediate]
      _ = phaseSignedMomentum (spectatorBranch right.1)
          (spectatorMomentum right.1) := by
        rw [right.2.1.1]
        abel
  have hspectator :
      spectatorMomentum left.1 = spectatorMomentum right.1 := by
    apply phaseSignedMomentum_injective (spectatorBranch left.1)
    rw [← hspectatorBranch] at hsignedSpectator
    exact hsignedSpectator
  apply Subtype.ext
  apply Prod.ext
  · exact hslot
  · apply Prod.ext
    · exact hbranches
    · funext modeSlot
      fin_cases modeSlot
      · exact houtput
      · exact hintermediate
      · exact hspectator
      · exact hinnerLeft
      · exact hinnerRight

/-- Correct fixed-output dimension: the complete supported family is at most
`32 * N^2`, since it has two free momenta rather than three. -/
theorem card_fixedOutputSupportedEffectiveFourWaveDiagram_le
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputSupportedEffectiveFourWaveDiagram N output) ≤
      32 * N ^ 2 := by
  calc
    Fintype.card (FixedOutputSupportedEffectiveFourWaveDiagram N output) ≤
        Fintype.card (FixedOutputTwoVertexParameter N) :=
      Fintype.card_le_of_injective fixedOutputTwoVertexParameter
        fixedOutputTwoVertexParameter_injective
    _ = 32 * N ^ 2 := by
      simp [FixedOutputTwoVertexParameter, ZMod.card]
      ring

/-! ## An actual lower-dimensional repeated/cancellation subclass -/

/-- Actual supported fixed-output diagrams with coincident inner leaves. -/
abbrev FixedOutputInnerLeafRepeatedDiagram
    (N : Nat) [NeZero N] (output : Site N) :=
  {diagram : FixedOutputSupportedEffectiveFourWaveDiagram N output //
    innerLeftMomentum diagram.1 = innerRightMomentum diagram.1}

noncomputable instance fixedOutputInnerLeafRepeatedDiagramFintype
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype (FixedOutputInnerLeafRepeatedDiagram N output) :=
  Fintype.ofFinite _

/-- Only one inner momentum remains free in the repeated-inner-leaf sector. -/
abbrev FixedOutputInnerRepeatedParameter (N : Nat) :=
  Fin 2 × ((Fin 4 → Fin 2) × Site N)

def fixedOutputInnerRepeatedParameter
    {N : Nat} [NeZero N] {output : Site N}
    (diagram : FixedOutputInnerLeafRepeatedDiagram N output) :
    FixedOutputInnerRepeatedParameter N :=
  (outerInsertionSlot diagram.1.1,
    (diagram.1.1.2.1, innerLeftMomentum diagram.1.1))

theorem fixedOutputInnerRepeatedParameter_injective
    {N : Nat} [NeZero N] {output : Site N} :
    Function.Injective
      (fixedOutputInnerRepeatedParameter (N := N) (output := output)) := by
  intro left right hparameter
  have hbase : left.1 = right.1 := by
    apply fixedOutputTwoVertexParameter_injective
    apply Prod.ext
    · exact congrArg (fun parameter ↦ parameter.1) hparameter
    · apply Prod.ext
      · exact congrArg (fun parameter ↦ parameter.2.1) hparameter
      · apply Prod.ext
        · exact congrArg (fun parameter ↦ parameter.2.2) hparameter
        · calc
            innerRightMomentum left.1.1 = innerLeftMomentum left.1.1 :=
              left.2.symm
            _ = innerLeftMomentum right.1.1 :=
              congrArg (fun parameter ↦ parameter.2.2) hparameter
            _ = innerRightMomentum right.1.1 := right.2
  exact Subtype.ext hbase

/-- Coincident inner leaves form an actual `O(N)` family at fixed output. -/
theorem card_fixedOutputInnerLeafRepeatedDiagram_le
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputInnerLeafRepeatedDiagram N output) ≤
      32 * N := by
  calc
    Fintype.card (FixedOutputInnerLeafRepeatedDiagram N output) ≤
        Fintype.card (FixedOutputInnerRepeatedParameter N) :=
      Fintype.card_le_of_injective fixedOutputInnerRepeatedParameter
        fixedOutputInnerRepeatedParameter_injective
    _ = 32 * N := by
      simp [FixedOutputInnerRepeatedParameter, ZMod.card]
      ring

/-- Opposite-signed coincident inner external legs, the literal same-mode
phase/conjugate cancellation subclass. -/
abbrev FixedOutputInnerLeafCancellationDiagram
    (N : Nat) [NeZero N] (output : Site N) :=
  {diagram : FixedOutputInnerLeafRepeatedDiagram N output //
    totalFourWaveSign diagram.1.1 2 ≠
      totalFourWaveSign diagram.1.1 3}

noncomputable instance fixedOutputInnerLeafCancellationDiagramFintype
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype (FixedOutputInnerLeafCancellationDiagram N output) :=
  Fintype.ofFinite _

/-- The cancellation subclass inherits the same `O(N)` bound. -/
theorem card_fixedOutputInnerLeafCancellationDiagram_le
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputInnerLeafCancellationDiagram N output) ≤
      32 * N := by
  calc
    Fintype.card (FixedOutputInnerLeafCancellationDiagram N output) ≤
        Fintype.card (FixedOutputInnerLeafRepeatedDiagram N output) :=
      Fintype.card_le_of_injective (fun diagram ↦ diagram.1)
        (fun _ _ h ↦ Subtype.ext h)
    _ ≤ 32 * N := card_fixedOutputInnerLeafRepeatedDiagram_le N output

/-! ## Complete repeated/cancelling count on the fixed-output 2↔2 shell -/

/-- Four external modes after eliminating the last mode on the fixed-output
`2 ↔ 2` shell. -/
def reducedTwoToTwoExternalModes
    {N : Nat} (output : Site N) (free : Site N × Site N) :
    Fin 4 → Site N :=
  ![output, free.1, free.2, output + free.1 - free.2]

/-- The four graph lines on which two of the four reduced external modes
coincide.  The last line is the equality of the two negative legs. -/
def IsDegenerateTwoToTwoFreePair
    {N : Nat} (output : Site N) (free : Site N × Site N) : Prop :=
  free.1 = output ∨
    free.2 = output ∨
    free.1 = free.2 ∨
    free.1 = 2 * free.2 - output

/-- The graph-line condition is exactly failure of injectivity of the four
external mode labels.  Thus it includes both repeated same-sign legs and
positive/negative same-mode cancellation. -/
theorem not_injective_reducedTwoToTwoExternalModes_iff
    {N : Nat} [NeZero N] (output : Site N) (free : Site N × Site N) :
    ¬ Function.Injective (reducedTwoToTwoExternalModes output free) ↔
      IsDegenerateTwoToTwoFreePair output free := by
  constructor
  · intro hnoninjective
    by_contra hdegenerate
    simp only [IsDegenerateTwoToTwoFreePair, not_or] at hdegenerate
    rcases hdegenerate with ⟨hfirstOutput, hsecondOutput,
      hfirstSecond, hnegativePair⟩
    apply hnoninjective
    have houtputFirst : output ≠ free.1 := Ne.symm hfirstOutput
    have houtputSecond : output ≠ free.2 := Ne.symm hsecondOutput
    have houtputLast : output ≠ output + free.1 - free.2 := by
      intro hequal
      apply hfirstSecond
      linear_combination -hequal
    have hfirstLast : free.1 ≠ output + free.1 - free.2 := by
      intro hequal
      apply hsecondOutput
      linear_combination hequal
    have hsecondLast : free.2 ≠ output + free.1 - free.2 := by
      intro hequal
      apply hnegativePair
      linear_combination -hequal
    intro leftSlot rightSlot hequal
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      simp_all [reducedTwoToTwoExternalModes]
  · intro hdegenerate hinjective
    rcases hdegenerate with hfirstOutput | hsecondOutput |
        hfirstSecond | hnegativePair
    · have hslots : (0 : Fin 4) = 1 := by
        apply hinjective
        simp [reducedTwoToTwoExternalModes, hfirstOutput]
      exact (by decide : (0 : Fin 4) ≠ 1) hslots
    · have hslots : (0 : Fin 4) = 2 := by
        apply hinjective
        simp [reducedTwoToTwoExternalModes, hsecondOutput]
      exact (by decide : (0 : Fin 4) ≠ 2) hslots
    · have hslots : (1 : Fin 4) = 2 := by
        apply hinjective
        simp [reducedTwoToTwoExternalModes, hfirstSecond]
      exact (by decide : (1 : Fin 4) ≠ 2) hslots
    · have hmodes :
          reducedTwoToTwoExternalModes output free 2 =
            reducedTwoToTwoExternalModes output free 3 := by
        change free.2 = output + free.1 - free.2
        rw [hnegativePair]
        ring
      have hslots : (2 : Fin 4) = 3 := hinjective hmodes
      exact (by decide : (2 : Fin 4) ≠ 3) hslots

noncomputable instance degenerateTwoToTwoFreePairFintype
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype {free : Site N × Site N //
      IsDegenerateTwoToTwoFreePair output free} :=
  Fintype.ofFinite _

/-- Parametrize the four degeneracy graph lines by one tag and one free
momentum. -/
def degenerateTwoToTwoFreePairFromTag
    {N : Nat} [NeZero N] (output : Site N)
    (tag : Fin 4) (mode : Site N) :
    {free : Site N × Site N //
      IsDegenerateTwoToTwoFreePair output free} :=
  ⟨if tag = 0 then (output, mode)
    else if tag = 1 then (mode, output)
    else if tag = 2 then (mode, mode)
    else (2 * mode - output, mode), by
      fin_cases tag <;> simp [IsDegenerateTwoToTwoFreePair]⟩

theorem degenerateTwoToTwoFreePairFromTag_surjective
    {N : Nat} [NeZero N] (output : Site N) :
    Function.Surjective (fun tagged : Fin 4 × Site N ↦
      degenerateTwoToTwoFreePairFromTag output tagged.1 tagged.2) := by
  rintro ⟨⟨first, second⟩, hdegenerate⟩
  rcases hdegenerate with hfirstOutput | hsecondOutput |
      hfirstSecond | hnegativePair
  · refine ⟨(0, second), ?_⟩
    change first = output at hfirstOutput
    apply Subtype.ext
    change (output, second) = (first, second)
    rw [hfirstOutput]
  · refine ⟨(1, first), ?_⟩
    change second = output at hsecondOutput
    apply Subtype.ext
    change (first, output) = (first, second)
    rw [hsecondOutput]
  · refine ⟨(2, first), ?_⟩
    change first = second at hfirstSecond
    apply Subtype.ext
    change (first, first) = (first, second)
    rw [hfirstSecond]
  · refine ⟨(3, second), ?_⟩
    change first = 2 * second - output at hnegativePair
    apply Subtype.ext
    change (2 * second - output, second) = (first, second)
    rw [hnegativePair]

/-- All repeated/cancelling free pairs occupy at most four one-dimensional
graph lines. -/
theorem card_degenerateTwoToTwoFreePair_le
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card {free : Site N × Site N //
        IsDegenerateTwoToTwoFreePair output free} ≤
      4 * N := by
  calc
    Fintype.card {free : Site N × Site N //
        IsDegenerateTwoToTwoFreePair output free} ≤
        Fintype.card (Fin 4 × Site N) :=
      Fintype.card_le_of_surjective
        (fun tagged : Fin 4 × Site N ↦
          degenerateTwoToTwoFreePairFromTag output tagged.1 tagged.2)
        (degenerateTwoToTwoFreePairFromTag_surjective output)
    _ = 4 * N := by simp [ZMod.card]

/-- Complete repeated/cancelling subset of the exact fixed-output shell,
expressed in its two free coordinates. -/
abbrev DegenerateTwoToTwoMomentumShell
    (N : Nat) [NeZero N] (output : Site N) :=
  {shell : TwoToTwoMomentumShell N output //
    IsDegenerateTwoToTwoFreePair output
      (shellModeOne shell, shellModeTwo shell)}

noncomputable instance degenerateTwoToTwoMomentumShellFintype
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype (DegenerateTwoToTwoMomentumShell N output) :=
  Fintype.ofFinite _

def degenerateTwoToTwoMomentumShellToFree
    {N : Nat} [NeZero N] {output : Site N}
    (shell : DegenerateTwoToTwoMomentumShell N output) :
    {free : Site N × Site N //
      IsDegenerateTwoToTwoFreePair output free} :=
  ⟨(shellModeOne shell.1, shellModeTwo shell.1), shell.2⟩

theorem degenerateTwoToTwoMomentumShellToFree_injective
    {N : Nat} [NeZero N] {output : Site N} :
    Function.Injective
      (degenerateTwoToTwoMomentumShellToFree
        (N := N) (output := output)) := by
  intro left right hfree
  apply Subtype.ext
  apply (freePairEquivTwoToTwoMomentumShell output).symm.injective
  exact congrArg Subtype.val hfree

/-- Complete fixed-output shell degeneracy is `O(N)`, compared with the exact
ambient shell cardinality `N^2`. -/
theorem card_degenerateTwoToTwoMomentumShell_le
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (DegenerateTwoToTwoMomentumShell N output) ≤
      4 * N := by
  exact (Fintype.card_le_of_injective
    degenerateTwoToTwoMomentumShellToFree
    degenerateTwoToTwoMomentumShellToFree_injective).trans
      (card_degenerateTwoToTwoFreePair_le N output)

/-! ## Separate one-to-three sign sector -/

/-- Output-positive and all three external input legs negative. -/
def IsOneToThreeExternalSignSector
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Prop :=
  totalFourWaveSign diagram 1 = .minus ∧
    totalFourWaveSign diagram 2 = .minus ∧
    totalFourWaveSign diagram 3 = .minus

/-- The remaining non-presented sign/degeneracy sector is retained as a
separate transparent predicate.  No counting or resonance claim about this
whole union is hidden in the one-to-three theorem below. -/
def IsRemainingFourWaveClassificationSector
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Prop :=
  IsTwoToTwoClassificationRemainder diagram ∧
    ¬ IsOneToThreeExternalSignSector diagram

/-- Three nonzero acoustic momenta satisfy strict subadditivity. -/
theorem periodicSineFrequency_three_sum_lt
    {N : Nat} [NeZero N] {first second third : Site N}
    (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hthird : third ≠ 0) :
    periodicSineFrequency N (first + second + third) <
      periodicSineFrequency N first +
        periodicSineFrequency N second +
        periodicSineFrequency N third := by
  by_cases hsum : first + second = 0
  · have hsecondPositive :=
      periodicSineFrequency_pos_of_ne_zero hsecond
    have hfirstPositive :=
      periodicSineFrequency_pos_of_ne_zero hfirst
    rw [hsum, zero_add]
    linarith
  · have houter := periodicSineFrequency_add_lt hsum hthird
    have hinner := periodicSineFrequency_add_lt hfirst hsecond
    linarith

/-- In the one-to-three sign sector, exact two-vertex momentum support says
the output momentum is the sum of the three input momenta. -/
theorem outputMomentum_eq_sum_of_oneToThree
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hsector : IsOneToThreeExternalSignSector diagram) :
    outputMomentum diagram =
      spectatorMomentum diagram + innerLeftMomentum diagram +
        innerRightMomentum diagram := by
  have hmomentum :=
    totalFourWaveMomentum_eq_zero_of_supported diagram hsupported
  unfold totalFourWaveMomentum signedFourierMomentum at hmomentum
  rw [Fin.sum_univ_four] at hmomentum
  simp only [totalFourWaveSign_zero, totalFourWaveModes_zero,
    totalFourWaveModes_one, totalFourWaveModes_two,
    totalFourWaveModes_three,
    hsector.1, hsector.2.1, hsector.2.2,
    interactionSignMomentum] at hmomentum
  linear_combination hmomentum

/-- The one-to-three acoustic mismatch is strictly negative whenever its
three input modes are nonzero.  This is the four-leg adapter to the existing
strict three-wave subadditivity result. -/
theorem totalFourWaveMismatch_lt_zero_of_oneToThree
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hsector : IsOneToThreeExternalSignSector diagram)
    (hspectator : spectatorMomentum diagram ≠ 0)
    (hinnerLeft : innerLeftMomentum diagram ≠ 0)
    (hinnerRight : innerRightMomentum diagram ≠ 0) :
    totalFourWaveMismatch diagram < 0 := by
  have hfrequency := periodicSineFrequency_three_sum_lt
    hspectator hinnerLeft hinnerRight
  rw [← outputMomentum_eq_sum_of_oneToThree diagram hsupported hsector]
    at hfrequency
  unfold totalFourWaveMismatch periodicSinePhaseMismatch
  rw [Fin.sum_univ_four]
  simp only [totalFourWaveSign_zero, totalFourWaveModes_zero,
    totalFourWaveModes_one, totalFourWaveModes_two,
    totalFourWaveModes_three, InteractionSign.coefficient_plus,
    one_mul, hsector.1, hsector.2.1, hsector.2.2,
    InteractionSign.coefficient_minus]
  linarith

/-- Hence no active one-to-three effective diagram lies on the exact
four-wave acoustic resonance shell. -/
theorem active_totalFourWaveMismatch_ne_zero_of_oneToThree
    {N : Nat} [NeZero N]
    (diagram : ActiveEffectiveFourWaveDiagram N)
    (hsector : IsOneToThreeExternalSignSector diagram.1) :
    totalFourWaveMismatch diagram.1 ≠ 0 := by
  exact ne_of_lt (totalFourWaveMismatch_lt_zero_of_oneToThree
    diagram.1 diagram.2.1 hsector
    (diagram.2.2 2) (diagram.2.2 3) (diagram.2.2 4))

end

end ArchonPhysics.EqualMassPeriodicFPUTFourWaveRemainderCounting
